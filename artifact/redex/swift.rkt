#lang racket/base

(require redex/reduction-semantics
         "core.rkt"
         "exn.rkt"
         "platform.rkt")

(provide Swift -->swift)

(define-extended-ev-system Swift
  #:def-reduction -->sys
  #:def-exn-reduction -->sys/exn
  #:with-base-lang Exn
  #:with-base-reduction -->exn

  (e ::= ....
     (async/lambda (x_!_ ...) e)
     (await e)
     (cancel e)
     (cancelled?))

  (v ::= ....
     (async/lambda (x_!_ ...) e))

  (E ::= .... (await E) (cancel E))
  (M ::= .... (await M) (cancel M))
  (G ::= .... (await G) (cancel G))

  #:binding-forms

  (async/lambda (x ...) e #:refers-to (shadow x ...)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->swift/core
  (reduction-relation
   Swift
   #:domain (t σ Q T P)

   [--> (t_0 σ_0 Q_0 T (FS_0 ... (thread (label (in-hole E ((async/lambda (x ..._1) e_body) v ..._1))) F ...) FS_1 ...))
        (t_1 σ_2 Q_1 T (FS_0 ... (thread (label (in-hole E x_task)) F ...) FS_1 ...))

        ;; XXX: tie to spawning context
        (where/error (σ_1 x_task v_task) (task:allocate-dependency σ_0 label))
        (where/error (x_fresh ...) (gensyms (σ_1 e_body) (x ...)))
        (where/error σ_2 (ext σ_1 (x_task v_task) (x_fresh v) ...))
        (where/error e_subst (substitute* e_body (x x_fresh) ...))
        (where/error Q_1 (Q:push Q_0 (x_task (lambda (null)
                                               (begin null
                                                      (reset
                                                       (begin
                                                         (catch (lambda (v_err)
                                                                  (task:set-failed! x_task v_err))
                                                                (task:set-done! x_task e_subst))
                                                         ;; XXX: cancel on destruction
                                                         (task:cancel-dependencies x_task)
                                                         ;; XXX: dynamic-extent enforcement
                                                         (task:wait-on-dependencies x_task)
                                                         (os/start-soon (task:get-dependents x_task)))))))))
        (where/error t_1 (step t_0))
        "async-app"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (await v_awaitable))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ... (thread (label (in-hole E
                                                     (if (task:is-completed? v_awaitable)
                                                         (task:get-result v_awaitable)
                                                         (shift k
                                                                (task:add-self-as-dependent!
                                                                 v_awaitable
                                                                 (label (task:continue-with v_awaitable k))))))) F ...) FS_1 ...))

        (where/error t_1 (step t_0))
        "await"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (cancel v_task))) F ...) FS_1 ...))
        (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (task:set-cancelled! v_task))) F ...) FS_1 ...))

        "cancel"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (cancelled?))) F ...) FS_1 ...))
        (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (task:cancelled? σ label))) F ...) FS_1 ...))

        "cancelled?"]))


(define -->sys/overrides
  (extend-reduction-relation
   -->sys/exn
   Swift

   [-->
    (t_0 σ_0 Q T (FS_0 ... (thread (label (in-hole E (os/io t v))) F ...) FS_1 ...))
    (t_1 σ_2 Q T (FS_0 ... (thread
                            (x_io (os/start-later (+ (os/time) t)
                                                  x_io
                                                  (lambda (none)
                                                    (begin (catch (lambda (e) (task:set-failed! x_io e))
                                                                  (begin none
                                                                         (task:set-done! x_io v)))
                                                           (os/start-soon (task:get-dependents x_io))))))
                            (label (in-hole E x_io)) F ...)
                  FS_1 ...))

    ;; XXX: add dependency edge
    (where/error (σ_1 x_io v_task) (task:allocate-dependency σ_0 label))
    (where/error σ_2 (ext1 σ_1 (x_io v_task)))
    (where/error t_1 (step t_0))
    "os/io"]))


(define -->swift
  (union-reduction-relations
   (make-big-step -->sys/overrides)
   -->swift/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "core.rkt" niceties)
           "utils.rkt"
           (prefix-in unit: rackunit)
           "fuzz/check.rkt"
           "fuzz/run.rkt")

  (define-syntax-rule (swift-->>= e v)
    (begin
      (test-->> -->swift #:equiv prog/equiv (async/main #:threads 2 e) v)
      (check-runtime-output compile-and-run-swift 'e v)))

  (define-syntax-rule (swift-->>∈ e results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->swift (async/main #:threads 2 e) results
                             #:iterations 1
                             #:extract-result program-output)))
      (check-runtime-in-set compile-and-run-swift 'e results))))

(module+ test
  (swift-->>=
   (os/block ((async/lambda () 42)))
   42)

  (swift-->>=
   (os/block ((async/lambda (x) x) 42))
   42)

  (swift-->>=
   (let* ([yield (async/lambda () (void))]
          [id (async/lambda (x)
                (begin
                  (await (yield))
                  x))])

     (os/block (id 42)))
   42)

  (swift-->>=
   (let* ([mk-t1 (async/lambda () (throw 42))]
          [mk-t2 (async/lambda (x)
                   (catch (lambda (v) v)
                          (begin
                            (await (mk-t1))
                            x)))])

     (os/block (mk-t2 0)))
   42)

  (swift-->>=
   (let ([work (async/lambda () (await (os/io 5 42)))])
     (os/block (work)))
   42)

  (swift-->>=
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (begin
                      (print (await (os/io 1 msg)))
                      (print (await (os/io 1 msg)))))])
       (os/block (work "A"))))
   "AA")

  (swift-->>=
   (let* ([work (async/lambda () (cancelled?))])
     (os/block (work)))
   #false)

  (swift-->>∈
   (trace-stdout (print)
     (let* ([worker (async/lambda ()
                      (letrec ([loop (lambda (i)
                                       (when (< i 3)
                                         (begin
                                           (await (os/io 1 (print "A")))
                                           (loop (+ 1 i)))))])
                        (loop 0)))]
            [main (async/lambda ()
                    (let ([w (worker)])
                      (begin (await (os/io 1 (void)))
                             (cancel w)
                             (catch (lambda (e) (print "C"))
                                    (await w)))))])
       (os/block (main))))
   '("C" "AC" "AAC" "AAAC" "AAA"))

  (swift-->>∈
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

  (swift-->>∈
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
