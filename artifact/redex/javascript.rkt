#lang racket

(require redex/reduction-semantics
         "core.rkt"
         "exn.rkt"
         "platform.rkt")

(provide Js -->js -->>js)

(define-extended-ev-system Js
  #:def-reduction -->sys
  #:def-exn-reduction -->sys/exn
  #:with-base-lang Exn
  #:with-base-reduction -->exn
  #:single-threaded
  #:serial-dispatch

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
        (where/error t_1 t_0)
        "async-app"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (await v_awaitable))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ... (thread (label (in-hole E
                                                     ;; SUSPENSION: static, always suspend (yield to the
                                                     ;; microtask queue). A *settled* task will never drain
                                                     ;; its waiters again, so schedule the continuation
                                                     ;; directly; otherwise park it in the task's waiters to
                                                     ;; be drained when it completes.
                                                     (shift k
                                                            (if (task:is-completed? v_awaitable)
                                                                (os/start-soon
                                                                 (list (list (ptr label)
                                                                             (task:continue-with v_awaitable k))))
                                                                (task:add-self-as-dependent!
                                                                 v_awaitable
                                                                 (label (task:continue-with v_awaitable k))))))) F ...) FS_1 ...))

        (where/error t_1 t_0)
        "await"]))

(define -->sys/overrides
  (extend-reduction-relation
   -->sys/exn
   Js
   ;; DESTRUCTION: awaited (the default for the platform)

   ;; SINGLE-THREADED: the event loop IS the root thread. This shadows the
   ;; platform sys/schedule (which dispatches into an empty worker slot --
   ;; a phantom second thread): the next microtask runs as a frame stacked
   ;; on the parked root, so run-to-completion is structural -- while a
   ;; frame sits on top of root this pattern cannot match. #:serial-dispatch
   ;; stays: its sys/signal gate (macrotasks wait for an empty stack AND a
   ;; drained microtask queue) is real JS loop semantics, verified against
   ;; node (two same-deadline timers: microtasks drain between the timer
   ;; callbacks). No cancelled variant: JS has no cancel, task:cancelled?
   ;; is never true.
   [-->
    (t_0 σ Q_0 T ((thread (root (in-hole E (os/block v_task)))) FS ...))
    (t_1 σ Q_1 T ((thread (label_waiting (v_thunk (void)))
                          (root (in-hole E (os/block v_task))))
                  FS ...))

    (where #true (task:is-task? v_task))
    (where ((label_waiting v_thunk) Q_1) (Q:pop Q_0))
    (where/error t_1 t_0)
    "sys/schedule"]))

(define -->js
  (union-reduction-relations
   ;; REFERENCE STRENGTH: strong, the default GC rule keeps `Q` in the root set
   ;; PROPAGATION: await, no rule reraises unawaited exceptions
   ;; CANCELLATION: undefined
   (make-big-step -->sys/overrides)
   -->js/core))

;; Non-collapsing variant that exposes every successor (drops the make-big-step
;; wrapper). Drives whole-state-space exploration: the directed witness search
;; (fuzz/witness.rkt) and the reference enumerator (fuzz/reference.rkt).
(define -->>js
  (union-reduction-relations
   -->sys/overrides
   -->js/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "core.rkt" niceties)
           "utils.rkt"
           "fuzz/check.rkt"
           "fuzz/run.rkt")

  ;; #:threads 1: the model runs JS on a single P-slot (the root thread is
  ;; the event loop), matching the single-threaded runtime.
  (define-syntax-rule (js-->>∈ e results)
    (begin
      (evaluates-in-set -->js (async/main #:threads 1 e) results
                        #:extract-result program-output)
      (check-runtime-in-set compile-and-run-js 'e results)))

  (define-syntax-rule (js-->>= e v)
    (begin
      (test-->> -->js #:equiv prog/equiv (async/main #:threads 1 e) v)
      (check-runtime-output compile-and-run-js 'e v))))

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

  ;; The recursive loop must be an async/lambda: `await` in a sync lambda is
  ;; not valid JS (ReferenceError at runtime). And since `await` ALWAYS yields
  ;; to the microtask queue -- even on a settled promise -- the two workers
  ;; interleave one print per drain round after main's synchronous prefix:
  ;; "CABABAB" (node: 30/30; model enumeration: single final state, same).
  ;; The old sync-loop expectation "AAABBBC" encoded await-on-ready running
  ;; synchronously, which is not JS semantics.
  (js-->>=
   (trace-stdout (print)
     (let* ([get-truth (async/lambda () #true)]
            ;; print `msg` `n` times
            [work (async/lambda (msg n)
                    (let ([i 0])
                      (letrec ([loop (async/lambda ()
                                       (if (< i n)
                                           (begin (if (await (get-truth))
                                                      (print msg)
                                                      (void))
                                                  (set! i (+ i 1))
                                                  (await (loop)))
                                           (void)))])
                        (await (loop)))))]
            [main (async/lambda ()
                    (let ([task0 (work "A" 3)]
                          [task1 (work "B" 3)])
                      (begin (print "C")
                             (await task0)
                             (await task1))))])
       (os/block (main))))
   "CABABAB")

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
