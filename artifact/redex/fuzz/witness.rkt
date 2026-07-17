#lang racket/base

;; -----------------------------------------------------------------------------
;; Directed witness search over the model's reachable state graph.
;;
;; Enumerating a model's whole output set is infeasible for genuinely concurrent
;; programs: a few worker threads produce hundreds–thousands of inequivalent
;; interleavings, and no sound partial-order reduction collapses them (the
;; orderings carry real data dependencies through task-completion boxes and the
;; FIFO ready queue). See fuzz/reference.rkt and FUZZ.md.
;;
;; But the differential fuzzer does not need the whole set. Its oracle is
;; `real ⊆ model`: for each output the REAL runtime produced, can the MODEL
;; produce it? That is a single-target reachability question, and it is cheap in
;; the direction that matters.
;;
;; `multi-witness-search` decides ALL of a program's runtime outputs together
;; (see its header below). Per target it returns:
;;
;;   'producible    a witness execution was found (definitive yes).
;;   'unreachable   the target-consistent subgraph was exhausted with no match:
;;                  the model PROVABLY cannot produce the target (definitive no).
;;   'inconclusive  the search budget (states or time) ran out first (unknown),
;;                  or an exception truncated a subtree (a completed-but-
;;                  truncated search must not claim a proof).
;;
;; Finding a witness is cheap — prefix pruning walks essentially one path.
;; PROVING 'unreachable can cost as much as enumeration (it must exhaust the
;; pruned subgraph), which is why it is budgeted. For the oracle this is exactly
;; the right profile: confirming a real output is in the model is fast; the
;; expensive case arises only for a genuine divergence, where spending the budget
;; is warranted.
;; -----------------------------------------------------------------------------

(require redex/reduction-semantics
         racket/set
         racket/place
         (only-in racket/string string-prefix?)
         (only-in racket/list remove-duplicates)
         (only-in "model.rkt" canonicalize accumulator-value observed-output))

(provide multi-witness-search walk-battery)

;; ---------------------------------------------------------------------------
;; Memoized successor function.
;;
;; Successor lists are memoized, keyed on the canonical form of the state
;; (fuzz/model.rkt `canonicalize`: reachability-renamed, dead store entries
;; dropped, T deadline-sorted). Reduction always runs on RAW states — the
;; canonical form is only a lookup key, never reduced, so rules whose
;; enabledness inspects the whole store syntactically (asyncio's weak-Q
;; `sys/gc`) see exactly the state the model built. Two raw states with the
;; same key share one successor list; that is the same states-with-equal-keys-
;; are-interchangeable assumption the DFS dedup has always made, now also
;; letting the random walks (which heavily revisit prefix states near the
;; root) pay the matcher cost once per canonical state.
;;
;; Rule firings freshen names, so a raw successor list carries α-twins; one
;; representative per canonical key is kept, cutting the branching every
;; consumer sees.
;;
;; `on-exn` is called when reduction of a state raises: that state's subtree
;; is truncated (its successor list is cached as empty), which must poison any
;; later 'unreachable claim built on top of it.
;; ---------------------------------------------------------------------------

(define (make-successors red [on-exn void])
  (define memo (make-hash)) ; canonical key -> (listof raw state)
  (lambda (s #:key [key (canonicalize s)])
    (hash-ref! memo key
               (lambda ()
                 (define raw (with-handlers ([exn:fail? (lambda (e)
                                                          (on-exn e)
                                                          '())])
                               (apply-reduction-relation red s)))
                 (define reps (make-hash))
                 (for ([s* (in-list raw)])
                   (hash-ref! reps (canonicalize s*) s*))
                 (hash-values reps)))))

;; ---------------------------------------------------------------------------
;; Walk engine: SET-pruned random walks. A state survives if its output so far
;; prefixes ANY unresolved target; a terminal state whose output matches an
;; unresolved target resolves it. Every walk works for every remaining target
;; at once. `resolve!` must remove the target from `unresolved`.
;;
;; RESERVOIR RESTARTS: a witness can need a narrow schedule window deep in
;; the trace; root-started walks re-roll every early choice to get there.
;; Each walk reservoir-samples the prefix-consistent states it passes, and
;; half of all restarts begin from a random reservoir state instead of the
;; root — concentrating tries on the deep tail (revisits are near-free via
;; the successor memo). Restarting from a reachable state keeps every walk a
;; real execution suffix, so witnesses remain genuine.
;;
;; LAGGARD BIAS: real schedulers starve one thread for long stretches (OS
;; preemption), and several real outputs need exactly that — e.g. a wake
;; dispatched to a worker that then stalls across the whole of main's
;; completion. A uniform walk holds a thread still for k consecutive choices
;; with probability ~2^-k; a third of walks instead pick one P slot up front
;; and refuse to advance it whenever an alternative successor exists. Bias
;; only shapes SAMPLING — every path taken is still a real execution.
;; ---------------------------------------------------------------------------

;; Did the transition s -> s* ADVANCE thread slot i? Filling an EMPTY slot
;; (dispatch) does not count — the laggard pattern is "work arrives at the
;; thread, then the OS doesn't run it", so dispatch must stay allowed or a
;; stalled worker could never have work to be stalled ON.
(define (advanced-thread? s s* i)
  (define (P-of st) (and (list? st) (= 5 (length st)) (list-ref st 4)))
  (define P0 (P-of s))
  (define P1 (P-of s*))
  (and (list? P0) (list? P1) (= (length P0) (length P1))
       (> (length P0) i)
       (let ([a (list-ref P0 i)] [b (list-ref P1 i)])
         (and (not (equal? a b))
              (pair? a) (> (length a) 1))))) ; slot had a frame before the step

(define (run-walks! successors start unresolved resolve! deadline
                    #:tries [tries 400])
  (define (prefix-ok? partial)
    (or (not (string? partial))
        (for/or ([t (in-mutable-set unresolved)])
          (and (string? t) (string-prefix? t partial)))))
  (define nthreads
    (if (and (list? start) (= 5 (length start)) (list? (list-ref start 4)))
        (length (list-ref start 4))
        1))
  (define reservoir (make-vector 64 #f))
  (define seen-states 0)
  (define (reservoir-note! s)
    (set! seen-states (add1 seen-states))
    (define slot (if (< seen-states 64) seen-states (random seen-states)))
    (when (< slot 64) (vector-set! reservoir slot s)))
  (define (reservoir-pick)
    (define live (for/list ([s (in-vector reservoir)] #:when s) s))
    (if (null? live) start (list-ref live (random (length live)))))
  (let try ([i 0])
    (when (and (< i tries)
               (not (set-empty? unresolved))
               (< (current-inexact-milliseconds) deadline))
      ;; The laggard re-rolls every ~30 steps: witnesses can need SEQUENTIAL
      ;; stalls of different threads (e.g. a worker stalled across main's
      ;; completion, then the root stalled while that worker's tail print
      ;; lands), which a single per-walk laggard cannot express.
      (define (roll-laggard)
        (and (> nthreads 1) (zero? (random 3)) (random nthreads)))
      (let loop ([s (if (or (< i 20) (zero? (random 2))) start (reservoir-pick))]
                 [n 0]
                 [laggard (roll-laggard)])
        (cond
          [(or (> n 2500)
               (and (zero? (modulo n 25))
                    (>= (current-inexact-milliseconds) deadline)))
           (void)]
          [else
           (define succs (successors s))
           (cond
             [(null? succs)
              (define o (observed-output s))
              (when (set-member? unresolved o) (resolve! o))]
             [else
              (define ok (for/list ([s* (in-list succs)]
                                    #:when (prefix-ok? (accumulator-value s*)))
                           s*))
              (define preferred
                (if laggard
                    (let ([still (for/list ([s* (in-list ok)]
                                            #:unless (advanced-thread? s s* laggard))
                                   s*)])
                      (if (pair? still) still ok))
                    ok))
              (when (pair? preferred)
                (define s* (list-ref preferred (random (length preferred))))
                (reservoir-note! s*)
                (loop s* (add1 n)
                      (if (zero? (modulo (add1 n) 30)) (roll-laggard) laggard)))])]))
      (try (add1 i)))))

;; Standalone walk phase over a fresh memo — the unit of work a place worker
;; runs (witness-place.rkt). Returns the targets it witnessed before the
;; deadline. Only ever ADDS 'producible verdicts, so it needs no poisoning
;; bookkeeping: a truncated walk just fails to witness.
(define (walk-battery red start targets walk-ms #:tries [tries 2000])
  (define deadline (+ (current-inexact-milliseconds) walk-ms))
  (define unresolved (list->mutable-set (remove-duplicates targets)))
  (define found '())
  (define successors (make-successors red))
  (run-walks! successors start unresolved
              (lambda (t) (set-remove! unresolved t) (set! found (cons t found)))
              deadline #:tries tries)
  found)

;; ---------------------------------------------------------------------------
;; Multi-target search
;;
;; All of a program's unresolved runtime outputs are searched TOGETHER: the
;; targets come from the same program, so their target-consistent subgraphs
;; overlap heavily, and per-target searches re-explore that shared region
;; once per target. Two phases over one budget:
;;
;;  1. Set-pruned random walks (run-walks! above), up to half the budget.
;;     With `#:pool`, the same walk battery additionally runs on every place
;;     worker in parallel with independent RNG (witness-place.rkt); their
;;     findings are merged before phase 2, so the DFS prune set starts as
;;     small as possible.
;;  2. One UNION-pruned DFS over the rest. Exhausting the union subgraph
;;     without the caps proves 'unreachable for every target not found —
;;     each target's own subgraph is contained in the union's. Shrinking the
;;     prune set as targets resolve mid-DFS is sound: a state pruned by the
;;     shrunk set cannot reach any REMAINING target. (Place results arrive
;;     before the DFS starts and only shrink its prune set; the DFS's own
;;     exhaustion argument is unchanged.)
;;
;; Returns a hash: target -> 'producible | 'unreachable | 'inconclusive.
;; ---------------------------------------------------------------------------

(define (multi-witness-search red start targets
                              #:state-cap [state-cap 100000]
                              #:time-cap  [time-cap-ms 10000]
                              #:pool      [pool '()]
                              #:lang      [lang #f])
  (define start-ms (current-inexact-milliseconds))
  (define verdicts (make-hash)) ; target -> verdict
  (define unresolved (list->mutable-set (remove-duplicates targets)))
  (define (resolve! tgt) (set-remove! unresolved tgt) (hash-set! verdicts tgt 'producible))
  (define (prefix-of-some? partial)
    (or (not (string? partial))
        (for/or ([t (in-mutable-set unresolved)])
          (and (string? t) (string-prefix? t partial)))))

  (define poisoned? #f)
  (define successors (make-successors red (lambda (_) (set! poisoned? #t))))

  ;; Farm the walk phase out to the pool (non-blocking), then run it locally.
  (define workers (if lang pool '()))
  (define walk-ms (quotient time-cap-ms 2))
  (for ([pl (in-list workers)])
    (place-channel-put pl (vector lang start (set->list unresolved) walk-ms)))

  ;; Phase 1 (local): set-pruned walks, up to half the budget
  (run-walks! successors start unresolved resolve! (+ start-ms walk-ms))

  ;; Merge the pool's findings; the workers reply at ~the same deadline the
  ;; local phase just hit, so this get blocks only for the skew.
  (for ([pl (in-list workers)])
    (for ([t (in-list (place-channel-get pl))])
      (when (set-member? unresolved t) (resolve! t))))

  ;; Phase 2: union-pruned DFS with the remaining budget
  (unless (set-empty? unresolved)
    (define seen (make-hash))
    (define count 0)
    (define capped? #f)
    (let/ec stop
      (define (dfs s)
        (when (prefix-of-some? (accumulator-value s))
          (when (or (>= count state-cap)
                    (> (- (current-inexact-milliseconds) start-ms) time-cap-ms))
            (set! capped? #t)
            (stop (void)))
          (define key (canonicalize s))
          (unless (hash-has-key? seen key)
            (hash-set! seen key #t)
            (set! count (add1 count))
            (define succs (successors s #:key key))
            (cond
              [(null? succs)
               (define o (observed-output s))
               (when (set-member? unresolved o)
                 (resolve! o)
                 (when (set-empty? unresolved) (stop (void))))]
              [else (for ([s* (in-list succs)]) (dfs s*))]))))
      (dfs start))
    (define leftover-verdict
      (if (or capped? poisoned?) 'inconclusive 'unreachable))
    (for ([t (in-mutable-set unresolved)])
      (hash-set! verdicts t leftover-verdict)))

  verdicts)
