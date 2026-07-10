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
;; `witness-search` looks for ONE execution whose output is `target`. It prunes
;; any branch whose output-so-far has already diverged from `target` — printing
;; only ever appends, so a divergent prefix can never recover — and dedups
;; canonical states. It returns:
;;
;;   'producible    a witness execution was found (definitive yes).
;;   'unreachable   the target-consistent subgraph was exhausted with no match:
;;                  the model PROVABLY cannot produce `target` (definitive no).
;;   'inconclusive  the search budget (states or time) ran out first (unknown).
;;
;; Finding a witness is cheap — the prefix pruning walks essentially one path.
;; PROVING 'unreachable can cost as much as enumeration (it must exhaust the
;; pruned subgraph), which is why it is budgeted. For the oracle this is exactly
;; the right profile: confirming a real output is in the model is fast; the
;; expensive case arises only for a genuine divergence, where spending the budget
;; is warranted.
;;
;; `discover-output-set` recovers much of the model's output set best-effort, by
;; witness-searching a candidate pool: the seed outputs plus their distinct
;; character permutations (most concurrent outputs are reorderings of the same
;; prints). It is SOUND — every returned output has a witness — but not complete:
;; an output outside the candidate pool, or a candidate that came back
;; 'inconclusive, is missed. The `discovery` it returns records whether the
;; result is complete over the pool.
;; -----------------------------------------------------------------------------

(require redex/reduction-semantics
         racket/set
         (only-in racket/string string-prefix?)
         (only-in racket/list remove-duplicates permutations append*)
         (only-in "model.rkt" canonicalize accumulator-value program-output))

(provide witness-search
         multi-witness-search
         discover-output-set
         (struct-out discovery))

;; ---------------------------------------------------------------------------
;; Single-target search
;; ---------------------------------------------------------------------------

;; Does `red` drive `start` to a terminal whose `program-output` is `target`?
;; -> 'producible | 'unreachable | 'inconclusive   (see file header).
;;
;; Prefix pruning is an optimization that applies when `target` is a string and
;; the program accumulates stdout: a state whose accumulator is not a prefix of
;; `target` cannot lead to `target`, so its subtree is skipped. When there is no
;; string accumulator (e.g. a value-returning program) the search is unpruned
;; and simply matches `program-output` at each terminal — correct, just slower.
;; Phase 0: prefix-pruned random walks. A walk that reaches a terminal with
;; the target output IS a witness (constructive, definitive); failure proves
;; nothing. Models with parallel/any-order dispatch have witness paths that
;; walks find in milliseconds where the exhaustive DFS frontier starves --
;; the walk restarts cheaply whenever a print diverges from the target.
(define (walk-phase red start target deadline-ms)
  (and
   (string? target)
   (for/or ([_ (in-range 200)])
     (and (< (current-inexact-milliseconds) deadline-ms)
          (let loop ([s start] [n 0])
            (cond
              ;; deadline is checked per STEP: one walk step costs ~10-30ms of
              ;; Redex matching, so a per-try check can overrun by an entire
              ;; 2500-step walk (tens of seconds).
              [(or (> n 2500)
                   (and (zero? (modulo n 25))
                        (>= (current-inexact-milliseconds) deadline-ms)))
               #f]
              [else
               (define succs (with-handlers ([exn:fail? (lambda (_) '())])
                               (apply-reduction-relation red s)))
               (cond
                 [(null? succs) (equal? (program-output s) target)]
                 [else
                  (define ok
                    (for/list ([s* (in-list succs)]
                               #:when (let ([p (accumulator-value s*)])
                                        (or (not (string? p)) (string-prefix? target p))))
                      s*))
                  (and (pair? ok)
                       (loop (list-ref ok (random (length ok))) (add1 n)))])]))))))

(define (witness-search red start target
                        #:state-cap [state-cap 100000]
                        #:time-cap  [time-cap-ms 10000])
  (define start-ms (current-inexact-milliseconds))
  (if (walk-phase red start target (+ start-ms (/ time-cap-ms 3)))
      'producible
      (witness-dfs red start target state-cap time-cap-ms start-ms)))

;; ---------------------------------------------------------------------------
;; Multi-target search
;;
;; All of a program's unresolved runtime outputs are searched TOGETHER: the
;; targets come from the same program, so their target-consistent subgraphs
;; overlap heavily, and per-target searches re-explore that shared region
;; once per target. Two phases over one budget:
;;
;;  1. SET-pruned random walks (a state survives if its output prefixes ANY
;;     unresolved target; a terminal matching one resolves it). Every walk
;;     works for every remaining target at once.
;;  2. One UNION-pruned DFS over the rest. Exhausting the union subgraph
;;     without the caps proves 'unreachable for every target not found —
;;     each target's own subgraph is contained in the union's. Shrinking the
;;     prune set as targets resolve mid-DFS is sound: a state pruned by the
;;     shrunk set cannot reach any REMAINING target.
;;
;; Returns a hash: target -> 'producible | 'unreachable | 'inconclusive.
;; ---------------------------------------------------------------------------

(define (multi-witness-search red start targets
                              #:state-cap [state-cap 100000]
                              #:time-cap  [time-cap-ms 10000])
  (define start-ms (current-inexact-milliseconds))
  (define verdicts (make-hash)) ; target -> verdict
  (define unresolved (list->mutable-set (remove-duplicates targets)))
  (define (resolve! tgt) (set-remove! unresolved tgt) (hash-set! verdicts tgt 'producible))
  (define (prefix-of-some? partial)
    (or (not (string? partial))
        (for/or ([t (in-mutable-set unresolved)])
          (and (string? t) (string-prefix? t partial)))))

  ;; Phase 1: set-pruned walks, up to half the budget
  (let ([deadline (+ start-ms (/ time-cap-ms 2))])
    (let try ([i 0])
      (when (and (< i 400)
                 (not (set-empty? unresolved))
                 (< (current-inexact-milliseconds) deadline))
        (let loop ([s start] [n 0])
          (cond
            [(or (> n 2500)
                 (and (zero? (modulo n 25))
                      (>= (current-inexact-milliseconds) deadline)))
             (void)]
            [else
             (define succs (with-handlers ([exn:fail? (lambda (_) '())])
                             (apply-reduction-relation red s)))
             (cond
               [(null? succs)
                (define o (program-output s))
                (when (set-member? unresolved o) (resolve! o))]
               [else
                (define ok (for/list ([s* (in-list succs)]
                                      #:when (prefix-of-some? (accumulator-value s*)))
                             s*))
                (when (pair? ok)
                  (loop (list-ref ok (random (length ok))) (add1 n)))])]))
        (try (add1 i)))))

  ;; Phase 2: union-pruned DFS with the remaining budget
  (unless (set-empty? unresolved)
    (define seen (make-hash))
    (define count 0)
    (define poisoned? #f)
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
            (define succs (with-handlers ([exn:fail? (lambda (_)
                                                       (set! poisoned? #t)
                                                       '())])
                            (apply-reduction-relation red s)))
            (cond
              [(null? succs)
               (define o (program-output s))
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

(define (witness-dfs red start target state-cap time-cap-ms start-ms)
  (define seen (make-hash))                ; canonical state -> #t
  (define count 0)
  ;; Default 'unreachable: completing the DFS having explored the whole
  ;; target-consistent subgraph without a match IS a proof of absence.
  (define outcome 'unreachable)
  ;; An exception while computing successors truncates that state's subtree,
  ;; so "explored everything" no longer holds -- a completed search can then
  ;; claim at most 'inconclusive, never a proof. (Found this the hard way: a
  ;; metafunction fault was being swallowed here, silently deleting
  ;; subtrees.)
  (define poisoned? #f)
  (define string-target? (string? target))
  (let/ec stop
    (define (dfs s)
      (define partial (and string-target? (accumulator-value s)))
      ;; prune once the accumulated output diverges from the target prefix
      (when (or (not (string? partial)) (string-prefix? target partial))
        (when (or (>= count state-cap)
                  (> (- (current-inexact-milliseconds) start-ms) time-cap-ms))
          (set! outcome 'inconclusive)
          (stop (void)))
        (define key (canonicalize s))
        (unless (hash-has-key? seen key)
          (hash-set! seen key #t)
          (set! count (add1 count))
          (define succs (with-handlers ([exn:fail? (lambda (_)
                                                     (set! poisoned? #t)
                                                     '())])
                          (apply-reduction-relation red s)))
          (cond
            [(null? succs)                       ; terminal
             (when (equal? (program-output s) target)
               (set! outcome 'producible)
               (stop (void)))]
            [else (for ([s* (in-list succs)]) (dfs s*))]))))
    (dfs start))
  (if (and poisoned? (eq? outcome 'unreachable)) 'inconclusive outcome))

;; ---------------------------------------------------------------------------
;; Best-effort set discovery
;; ---------------------------------------------------------------------------

;; producible : sorted list of outputs proven reachable (each has a witness)
;; complete?  : #t iff no candidate came back 'inconclusive — i.e. `producible`
;;              is the FULL set of reachable outputs WITHIN the candidate pool
;;              (outputs outside the pool are still not guaranteed)
;; probed     : number of candidates witness-searched
(struct discovery (producible complete? probed) #:transparent)

;; Permuting a seed of length n yields n! candidates; cap the length we expand so
;; the candidate pool cannot blow up factorially. Seeds longer than this (or
;; non-string seeds) are probed as-is.
(define max-permuted-length 6)           ; 6! = 720

(define (candidates-of seed)
  (cond
    [(and (string? seed) (<= (string-length seed) max-permuted-length))
     (remove-duplicates (map list->string (permutations (string->list seed))))]
    [else (list seed)]))

;; Discover reachable outputs by witness-searching the `seeds` and their
;; character permutations. Per-candidate budgets are passed through to
;; `witness-search`.
(define (discover-output-set red start seeds
                             #:state-cap [state-cap 100000]
                             #:time-cap  [time-cap-ms 10000])
  (define candidates (remove-duplicates (append* (map candidates-of seeds))))
  (define producible '())
  (define complete? #t)
  (for ([c (in-list candidates)])
    (case (witness-search red start c #:state-cap state-cap #:time-cap time-cap-ms)
      [(producible)   (set! producible (cons c producible))]
      [(inconclusive) (set! complete? #f)]
      [(unreachable)  (void)]))
  (discovery (sort producible string<?) complete? (length candidates)))
