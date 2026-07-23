#lang racket

(require redex/reduction-semantics
         "core.rkt"
         "rust.rkt"
         "platform.rkt")

(provide Smol -->smol -->>smol)

(define-extended-ev-system Smol
  #:def-reduction -->sys
  #:with-base-lang Rust
  #:with-base-reduction -->rs
  (e ::= .... (spawn e) (cancel e))
  (E ::= .... (spawn E) (cancel E))
  (M ::= .... (spawn M) (cancel M)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->smol/core
  (reduction-relation
   Smol
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

   ;; cancel of a NEVER-STARTED task: async-task closes an unpolled task in
   ;; place -- it is unlinked from the queue without running (no print, no
   ;; poll), and cancel().await resolves WITHOUT an executor round-trip, so
   ;; the caller's next statement runs before any queued task dispatches.
   ;; The waiter handle is allocated already-done so `(await (cancel t))`
   ;; completes inline. The general rule below stays applicable: the
   ;; executor may also have started the task concurrently, in which case
   ;; the flag-and-wait path is what really happens.
   [--> (t_0 σ_0 (any_qpre ... (x_t _) any_qpost ...) T
             (FS_0 ... (thread (label (in-hole E (cancel (name v_task (struct (self (ptr x_t)) any_field ...))))) F ...) FS_1 ...))
        (t_1 σ_2 (any_qpre ... any_qpost ...) T
             (FS_0 ... (thread (label (in-hole E
                                              (begin
                                                (task:set-done! x_t (struct [type "Err"] [value (void)]))
                                                (os/start-soon (task:get-dependents x_t))
                                                (task:set-done! x_w (void))
                                                x_w))) F ...) FS_1 ...))

        (where/error (σ_1 x_w v_w) (task:allocate σ_0))
        (where/error σ_2 (ext1 σ_1 (x_w v_w)))
        (where/error t_1 t_0)
        "cancel-unstarted"]

   ;; Task::cancel().await sets the cancelled flag on the caller's own poll --
   ;; INLINE, not through the executor queue (deferring the flag to a queued
   ;; canceller task lets already-queued wakeups of the target run first,
   ;; which the real runtime cannot do). The spawned waiter models only the
   ;; wind-down wait that `(await (cancel t))` observes: it resolves once the
   ;; target has settled.
   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (cancel v_task))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ... (thread (label (in-hole E
                                                     (begin
                                                       (task:set-cancelled! v_task)
                                                       (spawn ((async/lambda ()
                                                                 (begin (await v_task)
                                                                        (void)))))))) F ...) FS_1 ...))

        (where/error t_1 t_0)
        "cancel"]

   ;; The entry future: block_on drives it INLINE on the calling thread, in
   ;; parallel with the (single) executor thread -- it never goes through the
   ;; executor queue. Modeled by stacking the entry task's wrapper frame
   ;; directly on the root thread: same Ok-wrapping wrapper as spawn's thunk
   ;; (os/block-done unwraps it), minus the first-run cancellation hook
   ;; (nothing can cancel the entry).
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
   Smol

   ;; FREE-RUNNING CLOCK: wall time advances while threads run (the block_on
   ;; thread can be OS-preempted while the executor thread and timers
   ;; proceed) -- covered by the base fused sys/signal (platform.rkt), which
   ;; with serial? = #false delivers ANY pending timer at ANY state. See the
   ;; rationale in tokio.rkt.

   ;; REACTOR COMPLETIONS BYPASS THE EXECUTOR FIFO. A delivered timer's
   ;; wake thunk (io-wake shaped: settle the io task, wake its dependents)
   ;; runs on smol's REACTOR thread in reality, not on the executor -- so a
   ;; spawned-but-never-polled task sitting at the head of the executor
   ;; queue cannot delay an io completion. The base FIFO head-pop forced
   ;; exactly that: with Q = [unpolled-task, io-wake], main's wake-up could
   ;; never run first, making cancel-before-first-poll outputs PROVABLY
   ;; unreachable (found by the in-container fuzz, seed 270486700 smol[0]:
   ;; runtime "D|s6" -- cancel landing before the executor's first poll --
   ;; was exhaustion-proven unreachable, yet real smol on Linux produced
   ;; it). Any-position pop for io-wake-shaped entries only; ordinary task
   ;; entries keep the executor's real FIFO. Running the wake on the worker
   ;; slot is an interleaving over-approximation of the separate reactor
   ;; thread, the sound direction for the oracle (cf. sys/schedule-main).
   ;; (the io-wake shape below is task:set-done!'s EXPANSION -- it is a
   ;; macro, so the stored thunk carries the expanded set-box! pair)
   [-->
    (t_0 σ (any_qpre ... (label_io (name v_thunk (lambda (x_none) (begin x_none (begin (set-box! _ _) (set-box! _ "done")) (os/start-soon _))))) any_qpost ...) T
         ((thread F F_rs ...) ... (thread) FS_1 ...))
    (t_1 σ (any_qpre ... any_qpost ...) T
         ((thread F F_rs ...) ...
          (thread (label_io (v_thunk (void)))) FS_1 ...))

    (where #false (task:cancelled? σ label_io))
    (where/error t_1 t_0)
    "sys/schedule-reactor"]

   [-->
    (t_0 σ Q_0 T ((thread F F_rs ...) ... (thread) FS_1 ...))
    (t_1 σ Q_1 T ((thread F F_rs ...) ... (thread
                                           (label_waiting (begin (task:set-done! label_waiting (struct [type "Err"] [value (void)]))
                                                                 (os/start-soon (task:get-dependents label_waiting))))) FS_1 ...))

    (where ((label_waiting _) Q_1) (Q:pop Q_0))
    (where #true (task:cancelled? σ label_waiting))
    (where/error t_1 t_0)
    "sys/schedule-cancelled"]

   ;; A cancelled timer (ANY of them -- direct ellipsis match; the old
   ;; T:pop-cancelled metafunction faulted with two cancelled timers pending)
   ;; is drained from T and placed back on Q (modelling Drop releasing the
   ;; task's IO), where sys/schedule-cancelled settles it Err and wakes its
   ;; dependents. Without this rule a cancelled timer is a zombie in T and
   ;; os/block can never exit.
   [--> (t_0 σ Q_0 (any_th ... (t_c label v) any_tt ...) P)
        (t_1 σ Q_1 (any_th ... any_tt ...) P)

        (where #true (task:cancelled? σ label))
        (where/error Q_1 (Q:push Q_0 (label v)))
        (where/error t_1 t_0)
        "sys/signal-cancel"]

   ;; B3: block_on resumptions. The entry future is polled on the CALLING
   ;; thread: when main's wake-up is queued, it resumes as a frame on the
   ;; parked root -- in genuine parallel with the executor thread -- never on
   ;; the worker. Any-position pop: the reactor wakes the block_on thread
   ;; directly, so main's wake does not queue behind executor work. (The
   ;; base head-pop dispatch may still grab a main-labeled entry into the
   ;; worker; those orderings are an over-approximation the oracle
   ;; tolerates.)
   [-->
    (t_0 σ (any_qpre ... (x_main v_thunk) any_qpost ...) T
         ((thread (root (in-hole E (os/block (name v_task (struct (self (ptr x_main)) any_field ...)))))) FS ...))
    (t_1 σ (any_qpre ... any_qpost ...) T
         ((thread (x_main (v_thunk (void)))
                  (root (in-hole E (os/block v_task))))
          FS ...))

    (where/error t_1 t_0)
    "sys/schedule-main"]

   ;; block_on returns the moment the entry future settles -- it does NOT
   ;; wait for executor quiescence. Pending queue entries and timers are
   ;; ABANDONED (probed: a spawned task's remaining prints never appear once
   ;; main returns; 30/30), but workers may be MID-POLL: they keep running,
   ;; so their remaining prints can land after the root's final output --
   ;; the racy shutdown tail a detached executor thread produces. The
   ;; (field value ...) unwrap removes the entry task's JoinHandle Ok
   ;; wrapper.
   [--> (t_0 σ Q T ((thread (root (in-hole E (os/block v_awaitable)))) FS ...))
        (t_1 σ () () ((thread (root (in-hole E (field value (task:get-result v_awaitable))))) FS ...))
        (where #true (task:is-task? v_awaitable))
        (where #true (task:settled? σ v_awaitable))
        (where/error t_1 t_0)
        "os/block-done"]))


(define -->smol
  (union-reduction-relations
   (make-big-step -->sys/overrides)
   -->smol/core))

;; Non-collapsing variant that exposes every successor (drops the make-big-step
;; wrapper). Drives whole-state-space exploration: the directed witness search
;; (fuzz/witness.rkt) and the reference enumerator (fuzz/reference.rkt).
(define -->>smol
  (union-reduction-relations
   -->sys/overrides
   -->smol/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "core.rkt" niceties)
           "utils.rkt"
           (prefix-in unit: rackunit)
           "fuzz/check.rkt"
           "fuzz/run.rkt")

  (define-syntax-rule (smol-->>= e v)
    (begin
      (test-->> -->smol #:equiv prog/equiv (async/main #:threads 2 e) v)
      (check-runtime-output compile-and-run-smol 'e v #:rust? #t)))

  (define-syntax-rule (smol-->>∈ e results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->smol (async/main #:threads 2 e) results
                             #:extract-result program-output)))
      (check-runtime-in-set compile-and-run-smol 'e results #:rust? #t)))

  ;; Model outputs checked against a REGEXP, runtime outputs against the
  ;; observed set: under the free-running clock (fused sys/signal) a program whose
  ;; output is bounded only by timing has an unbounded model set (at-least-n
  ;; sleeps can lag any amount), while real jitter stays small.
  (define-syntax-rule (smol-->>~ e px results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->smol (async/main #:threads 2 e) (list px)
                             #:extract-result program-output
                             #:equiv? (lambda (got pat) (regexp-match? pat got)))))
      (check-runtime-in-set compile-and-run-smol 'e results #:rust? #t))))

(module+ test
  (smol-->>=
   (trace-stdout (print)
     (let* ([suspend (async/lambda () (void))]
            [work (async/lambda (msg)
                    (begin (await (suspend))
                           (print msg)))]
            [c (work "A")])
       (os/block c)))
   "A")

  (smol-->>=
   (let* ([work (async/lambda ()
                  (await (os/io 1 42)))])
     (os/block (work)))
   42)

  (smol-->>=
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))])
     (os/block (work)))
   42)

  ;; Awaiting a JoinHandle yields a Result; unwrap its value to recover 42.
  (smol-->>=
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))]
          [main (async/lambda () (field value (await (spawn (work)))))])
     (os/block (main)))
   42)

  (smol-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda () (print "A"))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (os/block (transparent))))
   "B")

  (smol-->>~
   (trace-stdout (print)
     (let* ([work (async/lambda ()
                    (letrec ([loop (async/lambda ()
                                     (begin (await (os/io 1 (print "A")))
                                            (await (loop))))])
                      (await (loop))))]

            [main (async/lambda ()
                    (let ([t (spawn (work))])
                      (begin (await (os/io 2 (void)))
                             (await (cancel t)))))])
       (os/block (main))))
   #px"^A*$"
   (for/list ([i (in-range 5)])
     (make-string i #\A)))

  (smol-->>=
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

  (smol-->>∈
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
