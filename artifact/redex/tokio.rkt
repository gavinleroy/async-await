#lang racket

(require redex/reduction-semantics
         "core.rkt"
         "rust.rkt"
         "platform.rkt")

(provide Tokio -->tokio)

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
                                              (task:set-done! x_task (await v_coro))
                                              (os/start-soon (task:get-dependents x_task)))))))))
        (where/error t_1 (step t_0))
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
        (where/error t_1 (step t_0))
        "await-task"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (cancel v_task))) F ...) FS_1 ...))
        (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (task:set-cancelled! v_task))) F ...) FS_1 ...))
        "cancel"]

   [--> (t_0 σ Q T (FS_0 ... (thread (root (in-hole E (os/block (name v_coro (lambda (x) e))))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ... (thread (root (in-hole E (os/block (spawn v_coro)))) F ...) FS_1 ...))

        (where/error t_1 (step t_0))
        "os/block-coro"]))

(define -->sys/overrides
  (extend-reduction-relation
   -->sys
   Tokio

   [--> (t_0 σ Q_0 T ((thread F F_rs ...) ... (thread) FS_1 ...))
        (t_1 σ Q_1 T ((thread F F_rs ...) ...
                      (thread (label_waiting (if (task:is-cancelled? label_waiting)
                                                 ;; XXX: if a task is cancelled just throw it out
                                                 (void)
                                                 (v_thunk (void))))) FS_1 ...))

        (where ((label_waiting v_thunk) Q_1) (Q:pop Q_0))
        (where/error t_1 (step t_0))
        "sys/schedule"]


   [-->
    (t_0 σ Q_0 T ((thread F F_rs ...) ... (thread) FS_1 ...))
    (t_1 σ Q_1 T ((thread F F_rs ...) ... (thread) FS_1 ...))
    (where ((label_waiting _) Q_1) (Q:pop Q_0))
    (where #true (task:cancelled? σ label_waiting))
    (where/error t_1 (step t_0))
    "sys/schedule-cancelled"]

   [--> (t_0 σ Q T_0 P)
        (t_1 σ Q T_1 P)

        (where (some (_ _ T_1)) (T:pop-cancelled σ T_0))
        (where/error t_1 (step t_0))
        "sys/signal-cancel"]))


(define -->tokio
  (union-reduction-relations
   (make-big-step -->sys/overrides)
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
      (check-runtime-output compile-and-run-tokio 'e v)))

  (define-syntax-rule (tokio-->>∈ e results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->tokio (async/main #:threads 2 e) results
                             #:extract-result program-output)))
      (check-runtime-in-set compile-and-run-tokio 'e results))))

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

  (tokio-->>=
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))]
          [main (async/lambda () (await (spawn (work))))])
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

  (tokio-->>∈
   (trace-stdout (print)
     (let* ([work (async/lambda ()
                    (letrec ([loop (lambda ()
                                     (begin (await (os/io 1 (print "A")))
                                            (loop)))])
                      (loop)))]

            [main (async/lambda ()
                    (let ([t (spawn (work))])
                      (begin (await (os/io 2 (void)))
                             (cancel t))))])
       (os/block (main))))
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
