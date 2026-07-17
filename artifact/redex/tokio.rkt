#lang racket

(require redex/reduction-semantics
         "core.rkt"
         "rust.rkt"
         "platform.rkt")

(provide Tokio -->tokio -->>tokio)

(define-extended-ev-system Tokio
  #:def-reduction -->sys
  #:with-base-lang Rust
  #:with-base-reduction -->rs
  (e ::= .... (spawn e) (cancel e))
  (E ::= .... (spawn E) (cancel E))
  (M ::= .... (spawn M) (cancel M)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->tokio/core
  (reduction-relation
   Tokio
   #:domain (t σ Q T P)

   [--> (t_0 σ_0 Q_0 T (FS_0 ... (thread (label (in-hole E (spawn v_coro))) F ...) FS_1 ...))
        (t_1 σ_2 Q_1 T (FS_0 ... (thread (label (in-hole E x_task)) F ...) FS_1 ...))

        (where/error (σ_1 x_task v_task) (task:allocate σ_0))
        (where/error σ_2 (ext1 σ_1 (x_task v_task)))
        (where/error Q_1 (Q:push Q_0
                                 (x_task
                                  (lambda (none)
                                    (begin none
                                           (reset
                                            (begin
                                              (task:set-done! x_task (struct [type "Ok"] [value (await v_coro)]))
                                              (os/start-soon (task:get-dependents x_task)))))))))
        (where/error t_1 t_0)
        "spawn"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (await v_awaitable))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ...
                    (thread (label (in-hole E
                                            (if (task:is-completed? v_awaitable)
                                                (task:get-result v_awaitable)
                                                (shift k
                                                       (task:add-self-as-dependent!
                                                        v_awaitable
                                                        (label
                                                         (lambda (none)
                                                           (k (task:get-result v_awaitable))))))))) F ...) FS_1 ...))

        (where #true (task:is-task? v_awaitable))
        (where/error t_1 t_0)
        "await-task"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (cancel v_task))) F ...) FS_1 ...))
        (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (task:set-cancelled! v_task))) F ...) FS_1 ...))
        "cancel"]

   ;; The entry future: block_on (the #[tokio::main] expansion) drives it
   ;; INLINE on the calling thread, in parallel with the worker threads -- it
   ;; never goes through the run queue (probed: entry and every resumption on
   ;; ThreadId(1); workers elsewhere). Modeled by stacking the entry task's
   ;; Ok-wrapping frame directly on the root thread; os/block-done unwraps
   ;; it. No first-run cancellation hook: nothing can abort the entry.
   [--> (t_0 σ_0 Q T ((thread (root (in-hole E (os/block (name v_coro (lambda (x) e)))))) FS ...))
        (t_1 σ_2 Q T ((thread (x_task (reset
                                       (begin
                                         (task:set-done! x_task (struct [type "Ok"] [value (await v_coro)]))
                                         (os/start-soon (task:get-dependents x_task)))))
                              (root (in-hole E (os/block x_task))))
                      FS ...))

        (where/error (σ_1 x_task v_task) (task:allocate σ_0))
        (where/error σ_2 (ext1 σ_1 (x_task v_task)))
        (where/error t_1 t_0)
        "os/block-coro"]))

(define -->sys/overrides
  (extend-reduction-relation
   -->sys
   Tokio

   ;; FREE-RUNNING CLOCK: wall time advances independently of thread progress
   ;; -- a runnable thread can be OS-preempted while workers and timers
   ;; proceed. The base os/block-wait only advances the clock at full
   ;; quiescence (empty queue, root blocked, workers idle), which PROVABLY
   ;; loses runtime outputs (fuzz seed 227726474 tokio[0]: "ABC|24" -- a
   ;; timer firing before a runnable-but-stalled main's next print -- was
   ;; enumeration-exhausted unreachable, yet the real runtime produced it).
   ;; The clock may jump to ANY pending deadline at ANY state; sys/signal
   ;; then delivers due timers. Serial event-loop models (asyncio/js/trio)
   ;; keep the quiescent clock: their one thread cannot be preempted by the
   ;; loop itself.
   [-->
    (t_0 σ Q ((t_a label_a v_a) ... (t_x label_x v_x) (t_b label_b v_b) ...) P)
    (t_x σ Q ((t_a label_a v_a) ... (t_x label_x v_x) (t_b label_b v_b) ...) P)
    (side-condition (< (term t_0) (term t_x)))
    "os/clock"]

   ;; ANY-ORDER DISPATCH: tokio's multi-threaded scheduler is work-stealing
   ;; (per-worker queues + LIFO slots + a global injector), so there is no
   ;; cross-task FIFO guarantee. Dispatch pops an ARBITRARY ready thunk into
   ;; an idle worker -- an over-approximation of the stealing structure,
   ;; the sound direction for the membership oracle.
   [--> (t_0 σ (any_qpre ... (label_waiting v_thunk) any_qpost ...) T
             ((thread F F_rs ...) ... (thread) FS_1 ...))
        (t_1 σ (any_qpre ... any_qpost ...) T
             ((thread F F_rs ...) ...
              (thread (label_waiting (v_thunk (void)))) FS_1 ...))

        (where #false (task:cancelled? σ label_waiting))
        (where/error t_1 t_0)
        "sys/schedule"]

   ;; B3: block_on resumptions -- the entry future is polled on the CALLING
   ;; thread (probed: every resumption on ThreadId(1)), so main's queued
   ;; wake-up resumes as a frame on the parked root, in parallel with the
   ;; workers. Any-position pop: the waker targets the block_on thread
   ;; directly, it does not queue behind worker dispatch.
   [-->
    (t_0 σ (any_qpre ... (x_main v_thunk) any_qpost ...) T
         ((thread (root (in-hole E (os/block (name v_task (struct (self (ptr x_main)) any_field ...)))))) FS ...))
    (t_1 σ (any_qpre ... any_qpost ...) T
         ((thread (x_main (v_thunk (void)))
                  (root (in-hole E (os/block v_task))))
          FS ...))

    (where/error t_1 t_0)
    "sys/schedule-main"]

   [-->
    (t_0 σ (any_qpre ... (label_waiting _) any_qpost ...) T
         ((thread F F_rs ...) ... (thread) FS_1 ...))
    (t_1 σ (any_qpre ... any_qpost ...) T
         ((thread F F_rs ...) ...
          (thread (label_waiting (begin (task:set-done! label_waiting (struct [type "Err"] [value (void)]))
                                        (os/start-soon (task:get-dependents label_waiting))))) FS_1 ...))
    (where #true (task:cancelled? σ label_waiting))
    (where/error t_1 t_0)
    "sys/schedule-cancelled"]

   ;; A cancelled timer (ANY of them -- direct ellipsis match; the old
   ;; T:pop-cancelled metafunction faulted with two cancelled timers pending)
   ;; is drained from T and placed back on Q, where sys/schedule-cancelled
   ;; settles it Err and wakes its dependents.
   [--> (t_0 σ Q_0 (any_th ... (t_c label v) any_tt ...) P)
        (t_1 σ Q_1 (any_th ... any_tt ...) P)

        (where #true (task:cancelled? σ label))
        (where/error Q_1 (Q:push Q_0 (label v)))
        (where/error t_1 t_0)
        "sys/signal-cancel"]

   ;; block_on returns the moment the entry future settles; the runtime then
   ;; shuts down -- queued tasks and pending timers are dropped un-polled,
   ;; but workers MID-POLL keep running, so their remaining prints can land
   ;; after the root's final output (the racy shutdown tail observed in
   ;; fuzzing). The (field value ...) unwrap removes the entry task's
   ;; JoinHandle Ok wrapper.
   [--> (t_0 σ Q T ((thread (root (in-hole E (os/block v_awaitable)))) FS ...))
        (t_1 σ () () ((thread (root (in-hole E (field value (task:get-result v_awaitable))))) FS ...))
        (where #true (task:is-task? v_awaitable))
        (where #true (task:settled? σ v_awaitable))
        (where/error t_1 t_0)
        "os/block-done"]))


(define -->tokio
  (union-reduction-relations
   (make-big-step -->sys/overrides)
   -->tokio/core))

;; Non-collapsing variant that exposes every successor (drops the make-big-step
;; wrapper). Drives whole-state-space exploration: the directed witness search
;; (fuzz/witness.rkt) and the reference enumerator (fuzz/reference.rkt).
(define -->>tokio
  (union-reduction-relations
   -->sys/overrides
   -->tokio/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "core.rkt" niceties)
           "utils.rkt"
           (prefix-in unit: rackunit)
           "fuzz/check.rkt"
           "fuzz/run.rkt")

  (define-syntax-rule (tokio-->>= e v)
    (begin
      (test-->> -->tokio #:equiv prog/equiv (async/main #:threads 2 e) v)
      (check-runtime-output compile-and-run-tokio 'e v #:rust? #t)))

  (define-syntax-rule (tokio-->>∈ e results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->tokio (async/main #:threads 2 e) results
                             #:extract-result program-output)))
      (check-runtime-in-set compile-and-run-tokio 'e results #:rust? #t)))

  ;; Model outputs checked against a REGEXP, runtime outputs against the
  ;; observed set: under the free-running clock (os/clock) a program whose
  ;; output is bounded only by timing has an unbounded model set (at-least-n
  ;; sleeps can lag any amount), while real jitter stays small.
  (define-syntax-rule (tokio-->>~ e px results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->tokio (async/main #:threads 2 e) (list px)
                             #:extract-result program-output
                             #:equiv? (lambda (got pat) (regexp-match? pat got)))))
      (check-runtime-in-set compile-and-run-tokio 'e results #:rust? #t))))

(module+ test
  (tokio-->>=
   (trace-stdout (print)
     (let* ([suspend (async/lambda () (void))]
            [work (async/lambda (msg)
                    (begin (await (suspend))
                           (print msg)))]
            [c (work "A")])
       (os/block c)))
   "A")

  (tokio-->>=
   (let* ([work (async/lambda ()
                  (await (os/io 1 42)))])
     (os/block (work)))
   42)

  (tokio-->>=
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))])
     (os/block (work)))
   42)

  ;; Awaiting a JoinHandle yields a Result; unwrap its value to recover 42.
  (tokio-->>=
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))]
          [main (async/lambda () (field value (await (spawn (work)))))])
     (os/block (main)))
   42)

  (tokio-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda () (print "A"))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (os/block (transparent))))
   "B")

  (tokio-->>~
   (trace-stdout (print)
     (let* ([work (async/lambda ()
                    (letrec ([loop (async/lambda ()
                                     (begin (await (os/io 1 (print "A")))
                                            (await (loop))))])
                      (await (loop))))]

            [main (async/lambda ()
                    (let ([t (spawn (work))])
                      (begin (await (os/io 2 (void)))
                             (cancel t))))])
       (os/block (main))))
   #px"^A*$"
   (for/list ([i (in-range 5)])
     (make-string i #\A)))

  (tokio-->>=
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (print (await (os/io 1 msg))))]
            [main (async/lambda ()
                    (let ([t1 (work "A")]
                          [t2 (work "B")])
                      (begin (print "C")
                             (await t1)
                             (await t2))))])
       (os/block (main))))
   "CAB")

  (tokio-->>∈
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (print (await (os/io 1 msg))))]
            [main (async/lambda ()
                    (let ([t1 (work "A")]
                          [t2 (spawn (work "B"))])
                      (begin (print "C")
                             (await t1)
                             (await t2))))])
       (os/block (main))))
   ; 'C' must *always* come before 'A'
   (filter (lambda (s) (before s #\C #\A))
           (string-permutations "ABC"))))
