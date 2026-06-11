#lang racket

(require redex
         "core.rkt"
         "rust.rkt"
         "platform.rkt")

(provide Smol -->smol)

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
        (t_1 σ Q T (FS_0 ... (thread (label (in-hole E
                                                     (spawn ((async/lambda ()
                                                               (begin (task:set-cancelled! v_task)
                                                                      (await v_task)
                                                                      (void))))))) F ...) FS_1 ...))

        (where/error t_1 (step t_0))
        "cancel"]

   [--> (t_0 σ Q T (FS_0 ... (thread (root (in-hole E (os/block (name v_coro (lambda (x) e))))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ... (thread (root (in-hole E (os/block (spawn v_coro)))) F ...) FS_1 ...))

        (where/error t_1 (step t_0))
        "os/block-coro"]))

(define -->sys/overrides
  (extend-reduction-relation
   -->sys
   Smol

   [-->
    (t_0 σ Q_0 T ((thread F F_rs ...) ... (thread) FS_1 ...))
    (t_1 σ Q_1 T ((thread F F_rs ...) ... (thread
                                           (label_waiting (begin (task:set-done! label_waiting "cancelled")
                                                                 (os/start-soon (task:get-dependents label_waiting))))) FS_1 ...))

    (where ((label_waiting _) Q_1) (Q:pop Q_0))
    (where #true (task:cancelled? σ label_waiting))
    (where/error t_1 (step t_0))
    "sys/schedule-cancelled"]))


(define -->smol
  (union-reduction-relations
   (make-big-step -->sys/overrides)
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
      (check-runtime-output compile-and-run-smol 'e v)))

  (define-syntax-rule (smol-->>∈ e results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->smol (async/main #:threads 2 e) results
                             #:extract-result program-output)))
      (check-runtime-in-set compile-and-run-smol 'e results))))

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

  (smol-->>=
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))]
          [main (async/lambda () (await (spawn (work))))])
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

  (smol-->>∈
   (trace-stdout (print)
     (let* ([work (async/lambda ()
                    (letrec ([loop (lambda ()
                                     (begin (await (os/io 1 (print "A")))
                                            (loop)))])
                      (loop)))]

            [main (async/lambda ()
                    (let ([t (spawn (work))])
                      (begin (await (os/io 2 (void)))
                             (await (cancel t)))))])
       (os/block (main))))
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
