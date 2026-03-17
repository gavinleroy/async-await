#lang racket/base

(require redex
         (only-in racket/list flatten)
         "core.rkt"
         "py.rkt"
         "platform.rkt")

(provide AsyncIO -->aio)

(define-extended-ev-system AsyncIO
  #:def-reduction -->sys
  #:def-exn-reduction -->sys/exn
  #:with-base-lang Py
  #:with-base-reduction -->py
  (e ::= .... (spawn e) (cancel e))
  (E ::= .... (spawn E) (cancel E))
  (M ::= .... (spawn M) (cancel M))
  (G ::= .... (spawn G) (cancel G)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->aio/core
  (reduction-relation
   AsyncIO
   #:domain (t σ Q T P)

   ;; EAGERNESS: lazy, a coroutine comes from the Py model when an async/lambda is applied
   [--> (t_0 σ_0 Q_0 T (FS_0 ... (thread (label (in-hole E (spawn v_coro))) F ...) FS_1 ...))
        (t_1 σ_2 Q_1 T (FS_0 ... (thread (label (in-hole E x_task)) F ...) FS_1 ...))

        (where/error (σ_1 x_task v_task) (task:allocate σ_0))
        (where/error σ_2 (ext1 σ_1 (x_task v_task)))
        (where/error Q_1 (Q:push Q_0
                                 (x_task
                                  (lambda (none)
                                    (reset
                                     (begin
                                       (catch (lambda (v_err) (task:set-failed! x_task v_err))
                                              (begin none (task:set-done! x_task (await v_coro))))
                                       (os/start-soon (task:get-dependents x_task))))
                                    ;; EXTENT: indefinite, at the end of the task scope we don't destroy
                                    ;; tasks that were spawned during the execution of `v_coro`.
                                    ))))
        (where/error t_1 (step t_0))
        "spawn"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (await v_awaitable))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ...
                    (thread (label (in-hole E
                                            (begin
                                              (task:set-awaited! v_awaitable)
                                              ;; SUSPENSION: dynamic, if the value is ready no need to suspend
                                              (if (task:is-completed? v_awaitable)
                                                  (task:get-result v_awaitable)
                                                  (shift k
                                                         (task:add-self-as-dependent!
                                                          v_awaitable
                                                          (label (task:continue-with v_awaitable k)))))))) F ...) FS_1 ...))

        (where #true (task:is-task? v_awaitable))
        (where/error t_1 (step t_0))
        "await-task"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (cancel v_task))) F ...) FS_1 ...))
        (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (task:set-cancelled! v_task))) F ...) FS_1 ...))
        "cancel"]

   [--> (t_0 σ Q T (FS_0 ... (thread (root (in-hole E (os/block (name v_coro (lambda (x) e))))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ... (thread (root (in-hole E (os/block (spawn v_coro)))) F ...) FS_1 ...))

        (where/error t_1 (step t_0))
        "os/block-coro"]))

(define -->sys/overriden
  (extend-reduction-relation
   -->sys/exn
   AsyncIO

   [-->
    (t_0 σ_0 Q_0 T ((thread F F_rs ...) ... (thread) FS_1 ...))
    (t_1 σ_1 Q_1 T ((thread F F_rs ...) ... (thread (label_waiting (throw-in v_thunk "cancelled"))) FS_1 ...))

    (where ((label_waiting v_thunk) Q_1) (Q:pop Q_0))
    (where #true (task:cancelled? σ label_waiting))
    ;; TODO: in asyncio tasks are edge triggered
    ;(where/error σ_1 (task:uncancel σ_0 label_waiting))
    (where/error t_1 (step t_0))
    "sys/schedule-cancelled"]

   ;; STRENGTH weak, `Q`, the Executor loop is not a part of the GC root set
   [--> (t_0 (any_before ... (x v) any_after ...) (any_0 ... (x _) any_1 ...) T PS)
        (t_1 (any_before ... any_after ...) (any_0 ... any_1 ...) T PS)
        (side-condition
         (let ([remaining-state (term (T PS any_before ... any_after ...))])
           (not (memq (term x) (flatten remaining-state)))))
        (where/error t_1 (step t_0))
        "sys/gc"]


   [--> (t_0 σ Q T ((thread (root (in-hole E (os/block v_task)))) FS ...))
        (t_1 σ Q T ((thread (root (in-hole E (begin
                                               (cancel x_0 x_1 ...)
                                               (os/block v_task))))) FS ...))

        (where #true (task:settled? σ v_task))
        (where (x_0 x_1 ...) (store:get-uncancelled-tasks σ))
        (where/error t_1 (step t_0))
        "os/block-cancel"]

   [--> (t_0 σ () () ((thread (root (in-hole E (os/block v_task)))) FS ...))
        (t_1 σ () () ((thread (root (in-hole E (task:get-result v_task)))) FS ...))

        (where #true (task:settled? σ v_task))
        (where () (store:get-uncancelled-tasks σ))
        (where none (store:find-unawaited-error σ))
        (where/error t_1 (step t_0))
        "os/block-exit"]

   [--> (t_0 σ () () ((thread (root (in-hole E (os/block v_task)))) FS ...))
        (t_1 σ () () ((thread (root (in-hole E (throw v_error)))) FS ...))

        (where #true (task:settled? σ v_task))
        ;; PROPAGATION: reraise, exceptions are reraised at the end of the jk
        (where (some v_error) (store:find-unawaited-error σ))
        (where/error t_1 (step t_0))
        "os/block-exit-throwing"]))

(define -->aio
  (union-reduction-relations
   (make-big-step -->sys/overriden)
   -->aio/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (prefix-in unit: rackunit)
           (submod "core.rkt" niceties)
           "utils.rkt")

  (define-syntax-rule (aio-->>= e v)
    (test-->> -->aio #:equiv prog/equiv (async/main #:threads 2 e) v))

  (define-syntax-rule (aio-->>∈ e results)
    (unit:check-true
     (with-exn-handler
         (evaluates-in-set -->aio (async/main #:threads 2 e) results
                           #:iterations 5
                           #:extract-result program-output))))

  (define-metafunction AsyncIO
    resume! : e e -> e
    [(resume! e_coro e_val)
     (e_coro e_val)]))

(module+ test
  (aio-->>=
   (resume! ((async/lambda (x) 42) 0) (void))
   42)

  (aio-->>=
   (trace-stdout (print)
     (let* ([suspend (async/lambda () (void))]
            [work (async/lambda (msg)
                    (begin (await (suspend))
                           (print msg)))]
            [c (work "A")])
       (os/block c)))
   "A")

  (aio-->>=
   (let* ([work (async/lambda ()
                  (await (os/io 1 42)))])
     (os/block (work)))
   42)

  (aio-->>=
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))])
     (os/block (work)))
   42)

  (aio-->>=
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))]
          [main (async/lambda () (await (spawn (work))))])
     (os/block (main)))
   42)

  (aio-->>=
   (let* ([exn (async/lambda ()
                 (throw "whoops"))]
          [main (async/lambda ()
                  (let ([t (spawn (exn))])
                    (await (os/io 1 42))))])
     (catch (lambda (e) e)
            (os/block (main))))
   "whoops")

  (aio-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda () (print "A"))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (os/block (transparent))))
   "B")

  (aio-->>∈
   (let* ([work (async/lambda () (await (os/io 20 0)))]
          [main (async/lambda ()
                  (let ([t (spawn (work))])
                    (begin
                      (cancel t)
                      (await t))))])
     (catch (lambda (e) "cancelled")
            (os/block (main))))
   '("cancelled" 0))

  (aio-->>=
   (let* ([mk-t1 (async/lambda () (throw 42))]
          [mk-t2 (async/lambda (x)
                   (catch (lambda (v) v)
                          (begin
                            (await (mk-t1))
                            x)))])

     (os/block (mk-t2 0)))
   42)

  (aio-->>∈
   (let* ([f0 (async/lambda () (await (os/io 1000000 0)))]
          [f1 (async/lambda () (await (spawn (f0))))]
          [f2 (async/lambda () (await (spawn (f1))))]
          [main (async/lambda ()
                  (catch (lambda (e) "cancelled")
                         (let ([t (spawn (f2))])
                           (begin
                             (await (os/io 1 (void)))
                             (cancel t)
                             (await t)))))])
     (os/block (main)))
   '("cancelled"))

  (aio-->>∈
   (let* ([work (async/lambda ()
                  (catch (lambda (e) 42)
                         (await (os/io 10 0))))]
          [t (spawn (work))]
          [main (async/lambda ()
                  (begin (cancel t)
                         (await t)))])
     (os/block (main)))
   '(42 0))

  (aio-->>=
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

  (aio-->>∈
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
