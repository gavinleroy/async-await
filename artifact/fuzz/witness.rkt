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
         racket/match
         (only-in racket/string string-prefix?)
         (only-in racket/list remove-duplicates partition make-list)
         (only-in "model.rkt" canonicalize canon-for-lang accumulator-value observed-output))

(provide multi-witness-search walk-battery)

;; ---------------------------------------------------------------------------
;; Memoized successor function.
;;
;; Successor lists are memoized, keyed on the canonical form of the state
;; (fuzz/model.rkt `canonicalize`: reachability-renamed, dead store entries
;; dropped, T deadline-sorted; `#:canon` selects `canonicalize/timeless` for
;; the parallel models, whose fused delivery makes time values dead — see
;; model.rkt). Reduction always runs on RAW states — the
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

;; DETERMINISTIC-SPINE COLLAPSING: a single-successor state cannot branch,
;; so chasing straight through it loses no reachable terminal. The search
;; then sees one state per scheduler choice instead of one per micro-step.
;; Output only appends along a chain, so end-of-chain prefix pruning is
;; exactly as sound as per-link pruning.
(define spine-fuel 300)

(define (make-successors red [on-exn void] #:canon [canon canonicalize])
  (define memo (make-hash)) ; canonical key -> (listof collapsed state)
  (define (raw-succs s)
    (with-handlers ([exn:fail? (lambda (e) (on-exn e) '())])
      (apply-reduction-relation red s)))
  (define (dedup raw)
    (define reps (make-hash))
    (for ([s* (in-list raw)])
      (hash-ref! reps (canon s*) s*))
    (hash-values reps))
  (define (chase s fuel)
    (define raw (raw-succs s))
    (cond
      [(null? raw) s]
      [(zero? fuel) s]
      [(null? (cdr raw)) (chase (car raw) (sub1 fuel))]
      [else
       (define uniq (dedup raw))
       (if (null? (cdr uniq)) (chase (car uniq) (sub1 fuel)) s)]))
  (lambda (s #:key [key (canon s)])
    (hash-ref! memo key
               (lambda ()
                 (map (lambda (s*) (chase s* spine-fuel))
                      (dedup (raw-succs s)))))))

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
;; with probability ~2^-k; a share of walks instead pick one P slot up front
;; and refuse to advance it whenever an alternative successor exists. Bias
;; only shapes SAMPLING — every path taken is still a real execution.
;;
;; PARKED-POOL BIAS: the other recurring real-schedule shape is the ROOT
;; racing ahead of the whole pool — main prints and cancels spawned tasks
;; before the scheduler's first poll of any of them (e.g. tokio "BA|0":
;; cancel lands pre-poll, so a task's body never prints). Uniform walks must
;; decline every dispatch for ~10 consecutive choices to see this. A share
;; of walks instead refuse to touch ANY non-root P slot (no dispatch, no
;; worker advance) while an alternative exists; system steps that leave P
;; alone (timer delivery into Q, root progress) stay preferred.
;;
;; GREEDY-PROGRESS BIAS: the walk knows the exact output it wants, and the
;; prefix filter already discards any successor that prints a WRONG next
;; character — so a successor that lengthens the accumulator is always
;; correct progress. A share of walks prefer such successors whenever one
;; exists (uniform otherwise), turning long choreographed print sequences
;; (e.g. swift "ECCCAAABBBDDD|15": thirteen prints in a specific
;; interleaving) from an exponential stall-dance into a near-deterministic
;; descent. Prints that must NOT happen (a cancelled task's tail) are still
;; covered: the wrong-print successors were pruned, so greeding toward the
;; next needed char never forces a forbidden one.
;;
;; CHUNK BIAS: real schedulers run each thread to its next suspension
;; before switching (cooperative run-to-completion), so the runtime's
;; DOMINANT output comes from exactly that schedule — which a uniform walk,
;; weighting every interleaving equally, samples with vanishing
;; probability (observed: smol "EACDB|81", the runtime's output on 20 of
;; 20 runs, resisted 300s of tube walks and needed 232s to witness). A
;; share of walks prefer successors that keep advancing the SAME P slot as
;; the previous step while one exists, reproducing the run-to-completion
;; shape; steps that advance no slot (timer delivery, dispatch) reset the
;; preference.
;; ---------------------------------------------------------------------------

;; Did the transition s -> s* ADVANCE thread slot i? Filling an EMPTY slot
;; (dispatch) does not count — the laggard pattern is "work arrives at the
;; thread, then the OS doesn't run it", so dispatch must stay allowed or a
;; stalled worker could never have work to be stalled ON.
(define (P-of st) (and (list? st) (= 5 (length st)) (list-ref st 4)))

(define (advanced-thread? s s* i)
  (define P0 (P-of s))
  (define P1 (P-of s*))
  (and (list? P0) (list? P1) (= (length P0) (length P1))
       (> (length P0) i)
       (let ([a (list-ref P0 i)] [b (list-ref P1 i)])
         (and (not (equal? a b))
              (pair? a) (> (length a) 1))))) ; slot had a frame before the step

;; Did the transition s -> s* touch any NON-ROOT P slot (dispatch into it or
;; advance it)? The root slot (first — os/block lives there, and e.g. tokio's
;; sys/schedule-main resumes main's continuation on it) is always exempt.
(define (touched-pool? s s*)
  (define P0 (P-of s))
  (define P1 (P-of s*))
  (and (list? P0) (list? P1) (= (length P0) (length P1)) (pair? P0)
       (for/or ([a (in-list (cdr P0))] [b (in-list (cdr P1))])
         (not (equal? a b)))))

;; Index of the (single) P slot that changed in s -> s*, or #f if none did
;; (a pure system step: timer delivery, gc) or the shape changed.
(define (changed-slot s s*)
  (define P0 (P-of s))
  (define P1 (P-of s*))
  (and (list? P0) (list? P1) (= (length P0) (length P1))
       (for/first ([a (in-list P0)] [b (in-list P1)] [i (in-naturals)]
                   #:unless (equal? a b))
         i)))

(define (q-labels st)
  (define Q (and (list? st) (= 5 (length st)) (list-ref st 2)))
  (if (list? Q)
      (for/list ([e (in-list Q)] #:when (pair? e)) (car e))
      '()))

(define (run-walks! successors start unresolved resolve! deadline
                    #:tries [tries 400])
  ;; Union pruning admits any prefix of any unresolved target, so a walk can
  ;; drift between targets and commit to none. Later walks (once the easy
  ;; targets have fallen) half the time FOCUS on one randomly chosen target:
  ;; pruning against that singleton confines the walk to the target's own
  ;; prefix tube, where the greedy bias descends almost deterministically.
  (define (make-prefix-ok focus)
    (lambda (partial)
      (or (not (string? partial))
          (if focus
              (string-prefix? focus partial)
              (for/or ([t (in-mutable-set unresolved)])
                (and (string? t) (string-prefix? t partial)))))))
  (define (pick-focus i)
    (and (> i 50) (zero? (random 2))
         (let ([ts (for/list ([t (in-mutable-set unresolved)] #:when (string? t)) t)])
           (and (pair? ts) (list-ref ts (random (length ts)))))))
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
      ;; The bias re-rolls periodically: witnesses can need SEQUENTIAL
      ;; stalls of different threads (e.g. a worker stalled across main's
      ;; completion, then the root stalled while that worker's tail print
      ;; lands), which a single per-walk bias cannot express. The period is
      ;; per-walk random: some witnesses need one thread starved across a
      ;; LONG stretch (~100 steps of everyone else's work), which a fixed
      ;; short period re-rolls away mid-stretch. Roll: 1/4 unbiased, 1/4
      ;; single-slot laggard, 1/4 parked pool, 1/4 greedy progress.
      ;; A bias is a CONJUNCTION of three independently-sampled constraints
      ;; — the resistant witnesses need conjunctions, which exclusive modes
      ;; cannot sample (e.g. tokio "AAB|s7" needs a never-polled task HELD
      ;; in Q for the whole run AND the root stalled across its siblings'
      ;; first prints AND run-to-completion chunking in between):
      ;;
      ;;   hold — a queued task label whose entry may not leave Q (the
      ;;     cancel family's core idiom: spawned, never polled, settled by a
      ;;     late cancel; parking the whole pool cannot express it when the
      ;;     SIBLINGS must run). Sampled from the current Q.
      ;;   lag  — one P slot not to advance; the ROOT half the time (cancels
      ;;     are root actions, and cancel-window outputs need the root
      ;;     parked between its print and its cancel — a uniform pick gives
      ;;     the root only 1/nthreads of the stalls).
      ;;   pref — a successor preference: 'greedy (extend the accumulator),
      ;;     'chunk (keep advancing the thread of the previous step —
      ;;     run-to-completion, the real scheduler's dominant shape), 'pool
      ;;     (touch no non-root slot), or none. Serial (single-slot) models
      ;;     keep only the prefs that shape their timer/dispatch orderings.
      ;;
      ;; Each constraint falls back to the unconstrained candidate set when
      ;; it would leave nothing, so conjunctions degrade gracefully.
      (define (roll-laggard s)
        (define hold (and (zero? (random 3))
                          (let ([ls (q-labels s)])
                            (and (pair? ls)
                                 (list-ref ls (random (length ls)))))))
        (define lag (and (> nthreads 1) (zero? (random 3))
                         (if (zero? (random 2))
                             0
                             (add1 (random (sub1 nthreads))))))
        (define pref (if (> nthreads 1)
                         (case (random 4)
                           [(0) #f] [(1) 'greedy] [(2) 'chunk] [(3) 'pool])
                         (case (random 3)
                           [(0) #f] [(1) 'greedy] [(2) 'chunk])))
        (list hold lag pref))
      (define reroll-period (+ 20 (random 130)))
      (define prefix-ok? (make-prefix-ok (pick-focus i)))
      (define s0 (if (or (< i 20) (zero? (random 2))) start (reservoir-pick)))
      (let loop ([s s0]
                 [n 0]
                 [laggard (roll-laggard s0)]
                 [last-slot #f])
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
              (define (narrow cands keep?)
                (let ([kept (for/list ([s* (in-list cands)] #:when (keep? s*)) s*)])
                  (if (pair? kept) kept cands)))
              (match-define (list hold lag pref) (or laggard (list #f #f #f)))
              (define c1
                (if hold
                    (narrow ok (lambda (s*)
                                 (not (and (memq hold (q-labels s))
                                           (not (memq hold (q-labels s*)))))))
                    ok))
              (define c2
                (if lag
                    (narrow c1 (lambda (s*) (not (advanced-thread? s s* lag))))
                    c1))
              (define preferred
                (case pref
                  [(greedy)
                   (let* ([len (lambda (st)
                                 (define a (accumulator-value st))
                                 (if (string? a) (string-length a) 0))]
                          [here (len s)])
                     (narrow c2 (lambda (s*) (> (len s*) here))))]
                  [(chunk)
                   (if last-slot
                       (narrow c2 (lambda (s*) (eqv? (changed-slot s s*) last-slot)))
                       c2)]
                  [(pool)
                   (narrow c2 (lambda (s*) (not (touched-pool? s s*))))]
                  [else c2]))
              (when (pair? preferred)
                (define s* (list-ref preferred (random (length preferred))))
                (reservoir-note! s*)
                (loop s* (add1 n)
                      (if (zero? (modulo (add1 n) reroll-period)) (roll-laggard s*) laggard)
                      (changed-slot s s*)))])]))
      (try (add1 i)))))

;; Standalone walk phase over a fresh memo — the unit of work a place worker
;; runs (witness-place.rkt). Returns the targets it witnessed before the
;; deadline. Only ever ADDS 'producible verdicts, so it needs no poisoning
;; bookkeeping: a truncated walk just fails to witness.
(define (walk-battery red start targets walk-ms
                      #:tries [tries 2000]
                      #:canon [canon canonicalize])
  (define deadline (+ (current-inexact-milliseconds) walk-ms))
  (define unresolved (list->mutable-set (remove-duplicates targets)))
  (define found '())
  (define successors (make-successors red #:canon canon))
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
  (define canon (canon-for-lang lang))
  (define successors (make-successors red (lambda (_) (set! poisoned? #t))
                                      #:canon canon))

  ;; Phase 0: thread ladder. A witness using at most k worker slots is a
  ;; witness for the full configuration (slots are symmetric; extras idle),
  ;; and the reduced spaces are orders of magnitude smaller. POSITIVE
  ;; verdicts only: exhausting a reduced space proves nothing about the
  ;; full one, so no negative verdict is recorded here.
  (define (reduce-worker-slots k)
    (match start
      [(list t σ Q T P)
       (define-values (empties rest)
         (partition (lambda (th) (equal? th '(thread))) P))
       (and (> (length empties) k)
            (list t σ Q T (append rest (make-list k '(thread)))))]
      [_ #f]))
  (define (ladder-dfs! start-k deadline)
    (define seen (make-hash))
    (define count 0)
    (let/ec stop
      (define (dfs s)
        (when (prefix-of-some? (accumulator-value s))
          (when (or (>= count state-cap)
                    (> (current-inexact-milliseconds) deadline))
            (stop (void)))
          (define key (canon s))
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
      (dfs start-k)))
  ;; k=1 gets the larger slice (its states are ~10x cheaper to expand than
  ;; full width); k=2 covers outputs that need real parallelism.
  (define (ladder-slice k)
    (if (= k 1)
        (min 120000 (quotient time-cap-ms 2))
        (min 30000 (quotient time-cap-ms 6))))
  ;; Configs already at ≤1 worker slot cannot be reduced: run the k=1 DFS on
  ;; the FULL start instead — for single-worker lanes this is the entire
  ;; space, and it is the only exhaustive phase those lanes get.
  (for ([k (in-list '(1 2))])
    (unless (set-empty? unresolved)
      (define start-k (or (reduce-worker-slots k)
                          (and (= k 1) start)))
      (when start-k
        (ladder-dfs! start-k (+ (current-inexact-milliseconds) (ladder-slice k))))))

  ;; Farm the walk phase out to the pool (non-blocking), then run it locally.
  ;; Walks get 3/4 of the budget: every real runtime output lands as a walk
  ;; find in practice (the classified stragglers included 190s walk finds),
  ;; while the DFS quarter is only decisive for genuine mismatches — which
  ;; are rare and can be re-proven offline with a dedicated budget.
  (define workers (if lang pool '()))
  (define walk-ms (quotient (* 3 time-cap-ms) 4))
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
          (define key (canon s))
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
