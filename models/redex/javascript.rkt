#lang racket

(require redex
         "core.rkt"
         "exn.rkt"
         "platform.rkt")

(provide Js -->js)

(define-extended-ev-system Js
  #:def-reduction -->sys
  #:def-exn-reduction -->sys/exn
  #:with-base-lang Exn
  #:with-base-reduction -->exn

  (e ::= ....
     (async/lambda (x_!_ ...) e)
     (await e))

  (v ::= ....
     (async/lambda (x_!_ ...) e))

  (E ::= .... (await E))
  (M ::= .... (await M))
  (G ::= .... (await G))

  #:binding-forms

  (async/lambda (x ...) e #:refers-to (shadow x ...)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->js/core
  (reduction-relation
   Js
   #:domain (t σ Q T P)

   [--> (t_0 σ_0 Q T (FS_0 ... (thread (label (in-hole E ((async/lambda (x ..._1) e_body) v ..._1))) F ...) FS_1 ...))
        (t_1 σ_2 Q T (FS_0 ... (thread
                                ;; EAGERNESS: eager, the function body is placed on the executing thread to evaluate
                                (x_task (reset
                                         (begin
                                           (catch (lambda (v_err) (task:set-failed! x_task v_err))
                                                  (task:set-done! x_task e_subst))
                                           (os/start-soon (task:get-dependents x_task))
                                           ;; EXTENT: indefinite, at the end of the task scope we don't destroy
                                           ;; tasks that were spawned during the execution of `v_coro`.
                                           )))
                                (label (in-hole E x_task)) F ...) FS_1 ...))

        (where/error (σ_1 x_task v_task) (task:allocate σ_0))
        (where/error (x_fresh ...) (gensyms (σ_1 e_body) (x ...)))
        (where/error σ_2 (ext σ_1 (x_task v_task) (x_fresh v) ...))
        (where/error e_subst (substitute* e_body (x x_fresh) ...))
        (where/error t_1 (step t_0))
        "async-app"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (await v_awaitable))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ... (thread (label (in-hole E
                                                     ;; SUSPENSION: static, always suspend
                                                     (shift k
                                                            (task:add-self-as-dependent!
                                                             v_awaitable
                                                             (label (task:continue-with v_awaitable k)))))) F ...) FS_1 ...))

        (where/error t_1 (step t_0))
        "await"]))

(define -->sys/overrides
  (extend-reduction-relation
   -->sys/exn
   Js
   ;; DESTRUCTION: awaited (the default for the platform)
   ))

(define -->js
  (union-reduction-relations
   ;; REFERENCE STRENGTH: strong, the default GC rule keeps `Q` in the root set
   ;; PROPAGATION: await, no rule reraises unawaited exceptions
   ;; CANCELLATION: undefined
   (make-big-step -->sys/exn)
   -->js/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "core.rkt" niceties)
           "utils.rkt")

  (define-syntax-rule (js-->>∈ e results)
    (evaluates-in-set -->js (async/main #:threads 2 e) results
                      #:extract-result program-output))

  (define-syntax-rule (js-->>= e v)
    (test-->> -->js #:equiv prog/equiv (async/main #:threads 1 e) v)))

(module+ test
  (js-->>=
   (os/block ((async/lambda () 42)))
   42)

  (js-->>=
   (os/block ((async/lambda (x) x) 42))
   42)

  (js-->>=
   (let* ([suspend (async/lambda () (void))]
          [id (async/lambda (x)
                (begin
                  (await (suspend))
                  x))])
     (os/block (id 42)))
   42)

  (js-->>=
   (let* ([mk-t1 (async/lambda ()
                   (throw 42))]
          [mk-t2 (async/lambda (x)
                   (catch (lambda (v) v)
                          (begin
                            (await (mk-t1))
                            x)))])

     (os/block (mk-t2 0)))
   42)

  (js-->>=
   (let ([work (async/lambda ()
                 (await (os/io 5 42)))])
     (os/block (work)))
   42)

  (js-->>=
   (let* ([mk-t1 (async/lambda () (throw 42))]
          [mk-t2 (async/lambda (x)
                   (catch (lambda (v) v)
                          (begin
                            (await (mk-t1))
                            x)))])

     (os/block (mk-t2 0)))
   42)

  (js-->>=
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (begin
                      (print (await (os/io 1 msg)))
                      (print (await (os/io 1 msg)))))])
       (os/block (work "A"))))
   "AA")

  (js-->>=
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
       (os/block (main))))
   "AAABBBC")

  (js-->>∈
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
       (os/block (main))))
   (list "AB" "BA"))

  (js-->>∈
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
       (os/block (main))))
   (string-permutations "ABC")))
