#lang racket

(require redex
         "core.rkt"
         "lc+exn.rkt"
         "platform.rkt")

(provide C# -->c#)

(define-extended-ev-system C#
  #:def-reduction -->c#/sys
  #:def-threaded-lang Sys
  #:with-base-lang LC+Exn
  #:with-base-reduction -->exn

  (e ::= ....
     (async/lambda (x_!_ ...) e)
     (await e)
     (block e))

  (v ::= ....
     (async/lambda (x_!_ ...) e))

  (E ::= ....
     (await E)
     (block E))

  (M ::= .... (await M))
  (G ::= .... (await G))

  #:binding-forms

  (async/lambda (x ...) e #:refers-to (shadow x ...)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->c#/async/await
  (reduction-relation
   C#
   #:domain (t σ Q T P)

   [--> (t_0 σ_0 Q T (FS_0 ... (thread (label (in-hole E ((async/lambda (x ..._1) e_body) v ..._1))) F ...) FS_1 ...))
        (t_1 σ_2 Q T (FS_0 ... (thread
                                (x_task (reset
                                         (begin
                                           (catch (lambda (v_err) (task:set-failed! x_task v_err))
                                                  (task:set-done! x_task e_subst))
                                           (os/start-soon (task:get-waiters x_task)))))
                                (label (in-hole E x_task)) F ...) FS_1 ...))

        (where/error (σ_1 v_task) (task:allocate σ_0 label))
        (where/error (x_task x_fresh ...) (gensyms (σ_1 e_body) (task x ...)))
        (where/error σ_2 (ext σ_1 (x_task v_task) (x_fresh v) ...))
        (where/error e_subst (substitute* e_body (x x_fresh) ...))
        (where/error t_1 (step t_0))
        "async-app"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (await v_awaitable))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ... (thread (label (in-hole E
                                                     (if (task:is-completed? v_awaitable)
                                                         (task:get-result v_awaitable)
                                                         (shift x_k
                                                                (task:add-waiter! v_awaitable
                                                                                  (label
                                                                                   (lambda (null)
                                                                                     (x_k (task:get-result v_awaitable))))))))) F ...) FS_1 ...))

        (where/error t_1 (step t_0))
        "await"]

   [--> (t_0 σ Q T ((thread (root (in-hole E (block v_awaitable)))) FS ...))
        (t_1 σ Q T ((thread (root (in-hole E (task:get-result v_awaitable)))) FS ...))

        (side-condition (term (task:settled? σ v_awaitable)))
        (where/error t_1 (step t_0))
        "block"]

   [--> (t_0 σ_0 Q T (FS_0 ... (thread (label (in-hole E (os/io t v))) F ...) FS_1 ...))
        (t_1 σ_2 Q T (FS_0 ... (thread
                                (x_io (os/start-later (+ (os/time) t)
                                                      x_io
                                                      (lambda (none)
                                                        (begin
                                                          none
                                                          (task:set-done! x_io v)
                                                          (os/start-soon (task:get-waiters x_io))))))

                                (label (in-hole E x_io)) F ...) FS_1 ...))

        (where/error (σ_1 v_task) (task:allocate σ_0 label))
        (where/error (x_io) (gensyms σ_1 (io)))
        (where/error σ_2 (ext1 σ_1 (x_io v_task)))
        (where/error t_1 (step t_0))
        "os/io"]))

#;
(define -->c#/sys
  (reduction-relation
   C#
   #:domain (t σ Q T P)

   [--> (t_0 σ Q T (_ ..._1 (thread (throw v)) _ ..._2))
        (t_1 σ Q T ((thread (throw v)) (thread) ..._1 (thread) ..._2))

        (where/error t_1 (step t_0))
        "sys/halt"]))


(define -->c#
  (union-reduction-relations -->c#/sys -->c#/async/await))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "core.rkt" niceties)
           "utils.rkt")

  (define-syntax-rule (c#-->>∈ e results)
    (evaluates-in-set -->c# (async/main #:threads 2 e) results
                      #:extract-result program-output))

  (define-syntax-rule (c#-->>= e v)
    (test-->> -->c# #:equiv prog/equiv (async/main #:threads 2 e) v)))

(module+ test
  (c#-->>=
   (block ((async/lambda () 42)))
   42)

  (c#-->>=
   (block ((async/lambda (x) x) 42))
   42)

  (c#-->>=
   (let* ([suspend (async/lambda () (void))]
          [id (async/lambda (x)
                (begin
                  (await (suspend))
                  x))])
     (block (id 42)))
   42)

  (c#-->>=
   (let* ([mk-t1 (async/lambda ()
                   (throw 42))]
          [mk-t2 (async/lambda (x)
                   (catch (lambda (v) v)
                          (begin
                            (await (mk-t1))
                            x)))])

     (block (mk-t2 0)))
   42)

  (c#-->>=
   (let ([work (async/lambda ()
                 (await (os/io 5 42)))])
     (block (work)))
   42)

  (c#-->>=
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (begin
                      (print (await (os/io 1 msg)))
                      (print (await (os/io 1 msg)))))])
       (block (work "A"))))
   "AA")

  (c#-->>=
   (trace-stdout (print)
     (let* ([get-truth (async/lambda () #true)]
            ;; print `msg` `n` times
            [work (async/lambda (msg n)
                    (let ([i 0])
                      (letrec ([loop (lambda ()
                                       (if (< i n)
                                           (begin (if (await (get-truth))
                                                      (print msg)
                                                      (void))
                                                  (set! i (+ i 1))
                                                  (loop))
                                           (void)))])
                        (loop))))]
            [main (async/lambda ()
                    (let ([task0 (work "A" 3)]
                          [task1 (work "B" 3)])
                      (begin (print "C")
                             (await task0)
                             (await task1))))])
       (block (main))))
   "AAABBBC")

  (c#-->>∈
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (begin (await (os/io 0 (void)))
                           (print msg)))]
            [main (async/lambda ()
                    (let ([task0 (work "A")]
                          [task1 (work "B")])
                      (begin
                        (await task0)
                        (await task1))))])
       (block (main))))
   (list "AB" "BA"))

  (c#-->>∈
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (begin (await (os/io 5 (void)))
                           (print msg)))]
            [main (async/lambda ()
                    (let ([task0 (work "A")]
                          [task1 (work "B")])
                      (begin (print "C")
                             (await task0)
                             (await task1))))])
       (block (main))))
   (string-permutations "ABC")))
