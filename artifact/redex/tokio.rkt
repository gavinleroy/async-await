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

   ;; block_on (the #[tokio::main] expansion) drives the entry future inline
   ;; on the calling thread, never via the run queue (probed: entry and every
   ;; resumption on ThreadId(1)). Ok-wrapping frame stacked on root; no
   ;; first-run cancel hook.
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

   ;; FREE-RUNNING CLOCK: wall time advances independently of thread progress;
   ;; base fused sys/signal (serial? #f) delivers any pending timer at any state.
   ;; A quiescent-only clock provably loses outputs: a timer firing before a
   ;; runnable-but-stalled main's next print is real but model-unreachable.

   ;; ANY-ORDER DISPATCH: tokio's work-stealing scheduler gives no cross-task
   ;; FIFO guarantee, so dispatch pops an arbitrary ready thunk into an idle
   ;; worker -- an over-approximation, the sound direction for the oracle.
   [--> (t_0 σ (any_qpre ... (label_waiting v_thunk) any_qpost ...) T
             ((thread F F_rs ...) ... (thread) FS_1 ...))
        (t_1 σ (any_qpre ... any_qpost ...) T
             ((thread F F_rs ...) ...
              (thread (label_waiting (v_thunk (void)))) FS_1 ...))

        (where #false (task:cancelled? σ label_waiting))
        (where/error t_1 t_0)
        "sys/schedule"]

   ;; Entry-future resumptions run on the calling thread (probed: every
   ;; resumption on ThreadId(1)), as a frame on the parked root. Any-position
   ;; pop: the waker targets the block_on thread directly, not worker dispatch.
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

   ;; A cancelled timer (any position) drains from T back onto Q, where
   ;; sys/schedule-cancelled settles it Err. Direct ellipsis match: a
   ;; metafunction here faults when two cancelled timers are pending.
   [--> (t_0 σ Q_0 (any_th ... (t_c label v) any_tt ...) P)
        (t_1 σ Q_1 (any_th ... any_tt ...) P)

        (where #true (task:cancelled? σ label))
        (where/error Q_1 (Q:push Q_0 (label v)))
        (where/error t_1 t_0)
        "sys/signal-cancel"]

   ;; block_on returns when the entry settles: queued tasks and pending
   ;; timers are dropped un-polled, but mid-poll workers keep running, so
   ;; their prints can land after root's final output. The (field value ...)
   ;; unwrap removes the entry task's JoinHandle Ok wrapper.
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
;; (../fuzz/witness.rkt) and the reference enumerator (../fuzz/reference.rkt).
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
           "differential.rkt")

  (define-syntax-rule (tokio-->>= e v)
    (begin
      (test-->> -->tokio #:equiv prog/equiv (async/main #:threads 2 e) v)
      (differential-output 'tokio 'e v #:rust? #t)))

  (define-syntax-rule (tokio-->>∈ e results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->tokio (async/main #:threads 2 e) results
                             #:extract-result program-output)))
      (differential-in-set 'tokio 'e results #:rust? #t)))

  ;; Model outputs are checked via regexp: the free-running clock makes
  ;; timing-bounded output sets unbounded, while real runtime jitter stays small.
  (define-syntax-rule (tokio-->>~ e px results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->tokio (async/main #:threads 2 e) (list px)
                             #:extract-result program-output
                             #:equiv? (lambda (got pat) (regexp-match? pat got)))))
      (differential-in-set 'tokio 'e results #:rust? #t))))

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
