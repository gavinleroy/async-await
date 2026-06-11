#lang racket/base

(require redex
         (only-in racket/list flatten)
         "core.rkt"
         "py.rkt"
         "platform.rkt")

(provide Trio -->trio)

(define-extended-ev-system Trio
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

(define -->trio/core
  (reduction-relation
   Trio
   #:domain (t σ Q T P)

   ;; EAGERNESS: lazy, a coroutine comes from the Py model when an async/lambda is applied
   [--> (t_0 σ_0 Q_0 T (FS_0 ... (thread (label (in-hole E (spawn v_coro))) F ...) FS_1 ...))
        (t_1 σ_2 Q_1 T (FS_0 ... (thread (label (in-hole E x_task)) F ...) FS_1 ...))

        (where/error (σ_1 x_task v_task) (task:allocate-dependency σ_0 label))
        (where/error σ_2 (ext1 σ_1 (x_task v_task)))
        (where/error Q_1 (Q:push Q_0
                                 (x_task
                                  (lambda (none)
                                    (reset
                                     (begin
                                       (catch (lambda (v_err) (task:set-failed! x_task v_err))
                                              (begin none (task:set-done! x_task (await v_coro))
                                                     ;; DESTRUCTION: awaited, tasks aren't cancelled here!
                                                     ;; EXTENT: dynamic, at the end of the task scope we don't destroy
                                                     ;; tasks that were spawned during the execution of `v_coro`.
                                                     (task:await-dependencies x_task)))
                                       (os/start-soon (task:get-dependents x_task))))
                                    ))))
        (where/error t_1 (step t_0))
        "spawn"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (await v_awaitable))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ...
                    (thread (label (in-hole E
                                            ;; SUSPENSION: dynamic, if the value is ready no need to suspend
                                            (if (task:is-completed? v_awaitable)
                                                (task:get-result v_awaitable)
                                                (shift k
                                                       (task:add-self-as-dependent!
                                                        v_awaitable
                                                        (label (task:continue-with v_awaitable k))))))) F ...) FS_1 ...))

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
   Trio

   [--> (t_0 σ_0 Q T (FS_0 ... (thread (label (in-hole E (os/io t v))) F ...) FS_1 ...))
        (t_1 σ_2 Q T (FS_0 ...
                      (thread (x_io (os/start-later (+ (os/time) t)
                                                    x_io
                                                    (lambda (none)
                                                      (begin
                                                        none
                                                        (task:set-done! x_io v)
                                                        (os/start-soon (task:get-dependents x_io))))))
                              (label (in-hole E x_io)) F ...) FS_1 ...))

        ;;; XXX: override, allocate-dependency
        (where/error (σ_1 x_io v_task) (task:allocate-dependency σ_0 label))
        (where/error σ_2 (ext1 σ_1 (x_io v_task)))
        (where/error t_1 (step t_0))
        "os/io"]

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
        "os/block-exit"]))

(define -->trio
  (union-reduction-relations
   (make-big-step -->sys/overriden)
   -->trio/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (prefix-in unit: rackunit)
           (submod "core.rkt" niceties)
           "utils.rkt"
           "fuzz/check.rkt"
           "fuzz/run.rkt")

  (define-syntax-rule (trio-->>= e v)
    (begin
      (test-->> -->trio #:equiv prog/equiv (async/main #:threads 2 e) v)
      (check-runtime-output compile-and-run-trio 'e v)))

  (define-syntax-rule (trio-->>∈ e results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->trio (async/main #:threads 2 e) results
                             #:iterations 5
                             #:extract-result program-output)))
      (check-runtime-in-set compile-and-run-trio 'e results))))

  (define-metafunction Trio
    resume! : e e -> e
    [(resume! e_coro e_val)
     (e_coro e_val)]))

(module+ test
  (trio-->>=
   (os/block ((async/lambda () 42)))
   42)

  (trio-->>=
   (os/block ((async/lambda (x) x) 42))
   42)

  (trio-->>=
   (let* ([yield (async/lambda () (void))]
          [id (async/lambda (x)
                (begin
                  (await (yield))
                  x))])

     (os/block (id 42)))
   42)

  (trio-->>=
   (let* ([mk-t1 (async/lambda () (throw 42))]
          [mk-t2 (async/lambda (x)
                   (catch (lambda (v) v)
                          (begin
                            (await (mk-t1))
                            x)))])

     (os/block (mk-t2 0)))
   42)

  (trio-->>=
   (let ([work (async/lambda () (await (os/io 5 42)))])
     (os/block (work)))
   42)

  (trio-->>=
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (begin
                      (print (await (os/io 1 msg)))
                      (print (await (os/io 1 msg)))))])
       (os/block (work "A"))))
   "AA")

  (trio-->>∈
   (trace-stdout (print)
     (let* ([worker (async/lambda ()
                      (letrec ([loop (lambda (i)
                                       (when (< i 3)
                                         (begin
                                           (await (os/io 1 (print "A")))
                                           (loop (+ 1 i)))))])
                        (loop 0)))]
            [main (async/lambda ()
                    (let ([w (spawn (worker))])
                      (begin (await (os/io 1 (void)))
                             (cancel w)
                             (catch (lambda (e) (print "C"))
                                    (await w)))))])
       (os/block (main))))
   '("C" "AC" "AAC" "AAAC" "AAA"))

  (trio-->>∈
   (trace-stdout (print)
     (let* ([get-truth (async/lambda () #true)]
            [work (async/lambda (msg)
                    (letrec ([loop (lambda (i)
                                     (when (< i 3)
                                       (begin
                                         (when (await (get-truth))
                                           (print msg))
                                         (loop (+ 1 i)))))])
                      (loop 0)))]
            [main (async/lambda ()
                    (let ([task0 (work "A")]
                          [task1 (work "B")])
                      (begin (print "C")
                             (await task0)
                             (await task1))))])
       (os/block (main))))
   (map (lambda (s) (string-append "C" s))
        (string-permutations "AAABBB")))

  (trio-->>∈
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
