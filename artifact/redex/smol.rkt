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

   ;; cancel of a never-started task settles it inline (no executor
   ;; round-trip); the general flag-and-wait rule below still covers the
   ;; started-concurrently case.
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

   ;; cancel().await sets the cancelled flag inline on the caller's poll, not
   ;; via a queued canceller -- queuing would let pending wakeups of the
   ;; target run first, which real smol cannot.
   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (cancel v_task))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ... (thread (label (in-hole E
                                                     (begin
                                                       (task:set-cancelled! v_task)
                                                       (spawn ((async/lambda ()
                                                                 (begin (await v_task)
                                                                        (void)))))))) F ...) FS_1 ...))

        (where/error t_1 t_0)
        "cancel"]

   ;; block_on drives the entry future inline on the calling thread, never
   ;; via the executor queue: wrapper frame stacked on root, minus spawn's
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
   Smol

   ;; Free-running clock: base fused sys/signal (serial? #f) delivers any
   ;; pending timer at any state. Rationale in tokio.rkt.

   ;; Reactor completions bypass the executor FIFO: timer wakes run on smol's
   ;; reactor thread, so an unpolled task at the queue head cannot delay them
   ;; (pure FIFO makes cancel-before-first-poll outputs unreachable, which real
   ;; smol produces). Pattern matches task:set-done!'s EXPANSION -- it is a macro.
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

   ;; A cancelled timer (any position) drains from T back onto Q so
   ;; sys/schedule-cancelled settles it Err; otherwise it is a zombie in T and
   ;; os/block never exits. Direct ellipsis match: a metafunction here faults
   ;; when two cancelled timers are pending.
   [--> (t_0 σ Q_0 (any_th ... (t_c label v) any_tt ...) P)
        (t_1 σ Q_1 (any_th ... any_tt ...) P)

        (where #true (task:cancelled? σ label))
        (where/error Q_1 (Q:push Q_0 (label v)))
        (where/error t_1 t_0)
        "sys/signal-cancel"]

   ;; Entry-future resumptions run on the calling thread, in parallel with
   ;; the executor. Any-position pop: the reactor wakes the block_on thread
   ;; directly, so main never queues behind executor work.
   [-->
    (t_0 σ (any_qpre ... (x_main v_thunk) any_qpost ...) T
         ((thread (root (in-hole E (os/block (name v_task (struct (self (ptr x_main)) any_field ...)))))) FS ...))
    (t_1 σ (any_qpre ... any_qpost ...) T
         ((thread (x_main (v_thunk (void)))
                  (root (in-hole E (os/block v_task))))
          FS ...))

    (where/error t_1 t_0)
    "sys/schedule-main"]

   ;; block_on returns when the entry settles: pending queue entries and
   ;; timers are abandoned (probed: an unfinished spawn's prints never appear
   ;; after main returns), but mid-poll workers keep running, so their prints
   ;; can land after root's final output.
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
;; (../fuzz/witness.rkt) and the reference enumerator (../fuzz/reference.rkt).
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
           "differential.rkt")

  (define-syntax-rule (smol-->>= e v)
    (begin
      (test-->> -->smol #:equiv prog/equiv (async/main #:threads 2 e) v)
      (differential-output 'smol 'e v #:rust? #t)))

  (define-syntax-rule (smol-->>∈ e results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->smol (async/main #:threads 2 e) results
                             #:extract-result program-output)))
      (differential-in-set 'smol 'e results #:rust? #t)))

  ;; Model outputs are checked via regexp: the free-running clock makes
  ;; timing-bounded output sets unbounded, while real runtime jitter stays small.
  (define-syntax-rule (smol-->>~ e px results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->smol (async/main #:threads 2 e) (list px)
                             #:extract-result program-output
                             #:equiv? (lambda (got pat) (regexp-match? pat got)))))
      (differential-in-set 'smol 'e results #:rust? #t))))

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
