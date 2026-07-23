#lang racket

(require redex/reduction-semantics
         "core.rkt"
         "exn.rkt"
         "platform.rkt")

(provide C# -->c# -->>c#)

(define-extended-ev-system C#
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
  (G ::= .... (await G)))

;; NO #:binding-forms: async/lambda elimination gensym-renames its
;; parameters against the whole (store, body) itself -- see the rationale in
;; lc.rkt.

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->c#/core
  (reduction-relation
   C#
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
        (where/error t_1 t_0)
        "async-app"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (await v_awaitable))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ... (thread (label (in-hole E
                                                     ;; SUSPENSION: dynamic, if the task if ready then execution continues
                                                     (if (task:is-completed? v_awaitable)
                                                         (task:get-result v_awaitable)
                                                         (shift k
                                                                (task:add-self-as-dependent!
                                                                 v_awaitable
                                                                 (label (task:continue-with v_awaitable k))))))) F ...) FS_1 ...))

        (where/error t_1 t_0)
        "await"]))

(define -->sys/overrides

  (extend-reduction-relation
   -->sys/exn
   C#

   ;; FREE-RUNNING CLOCK: wall time advances while thread-pool threads run --
   ;; covered by the base fused sys/signal (platform.rkt), which with
   ;; serial? = #false delivers ANY pending timer at ANY state. See the
   ;; rationale in tokio.rkt.

   ;; DESTRUCTION: terminated, the event loop can exit with tasks remaining in Q/T
   [-->
    (t_0 σ Q T ((thread (root (in-hole E (os/block v_awaitable)))) FS ..._1))
    (t_1 σ () () ((thread (root (in-hole E (task:get-result v_awaitable)))) (thread) ..._1))
    (where #true (task:is-task? v_awaitable))
    (where #true (task:settled? σ v_awaitable))
    (where/error t_1 t_0)
    "os/block-done"]))

(define -->c#
  (union-reduction-relations
   ;; REFERENCE STRENGTH: strong, the default GC rule keeps `Q` in the root set
   ;; PROPAGATION: await, no rule reraises unawaited exceptions
   ;; CANCELLATION: undefined
   (make-big-step -->sys/overrides)
   -->c#/core))

;; Non-collapsing variant that exposes every successor (drops the make-big-step
;; wrapper). Drives whole-state-space exploration: the directed witness search
;; (fuzz/witness.rkt) and the reference enumerator (fuzz/reference.rkt).
(define -->>c#
  (union-reduction-relations
   -->sys/overrides
   -->c#/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "core.rkt" niceties)
           "utils.rkt"
           "fuzz/check.rkt"
           "fuzz/run.rkt")

  (define-syntax-rule (c#-->>∈ e results)
    (begin
      (evaluates-in-set -->c# (async/main #:threads 2 e) results
                        #:extract-result program-output)
      (check-runtime-in-set compile-and-run-cs 'e results)))

  (define-syntax-rule (c#-->>= e v)
    (begin
      (test-->> -->c# #:equiv prog/equiv (async/main #:threads 2 e) v)
      (check-runtime-output compile-and-run-cs 'e v))))

(module+ test
  (c#-->>=
   (os/block ((async/lambda () 42)))
   42)

  (c#-->>=
   (let ([foo (async/lambda ()
                (begin (await (os/io 4 (void)))
                       42))])
     (os/block (foo)))
   42)


  (c#-->>=
   (os/block ((async/lambda (x) x) 42))
   42)

  (c#-->>=
   (let* ([suspend (async/lambda () (void))]
          [id (async/lambda (x)
                (begin
                  (await (suspend))
                  x))])
     (os/block (id 42)))
   42)

  (c#-->>=
   (let* ([mk-t1 (async/lambda ()
                   (throw 42))]
          [mk-t2 (async/lambda (x)
                   (catch (lambda (v) v)
                          (begin
                            (await (mk-t1))
                            x)))])

     (os/block (mk-t2 0)))
   42)

  (c#-->>=
   (let ([work (async/lambda ()
                 (await (os/io 5 42)))])
     (os/block (work)))
   42)

  (c#-->>=
   (let* ([mk-t1 (async/lambda () (throw 42))]
          [mk-t2 (async/lambda (x)
                   (catch (lambda (v) v)
                          (begin
                            (await (mk-t1))
                            x)))])

     (os/block (mk-t2 0)))
   42)

  (c#-->>=
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (begin
                      (print (await (os/io 1 msg)))
                      (print (await (os/io 1 msg)))))])
       (os/block (work "A"))))
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
       (os/block (main))))
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
       (os/block (main))))
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
       (os/block (main))))
   (string-permutations "ABC")))
