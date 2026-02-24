#lang racket/base

(require redex
         "core.rkt"
         "py.rkt"
         "platform.rkt")

(provide AsyncIO -->aio)

(define-extended-ev-system AsyncIO
  #:def-reduction -->aio/sys
  #:def-threaded-lang PySys
  #:with-base-lang Py
  #:with-base-reduction -->py
  (e ::= .... (spawn e) (cancel e) (block e))
  (E ::= .... (spawn E) (cancel E) (block E))
  (M ::= .... (spawn M) (cancel M) (block M))
  (G ::= .... (spawn G) (cancel G) (block G)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->aio/core
  (reduction-relation
   AsyncIO
   #:domain (t σ Q T P)

   [--> (t_0 σ_0 Q_0 T (FS_0 ... (thread (label (in-hole E (spawn v_coro))) F ...) FS_1 ...))
        (t_1 σ_2 Q_1 T (FS_0 ... (thread (label (in-hole E x_task)) F ...) FS_1 ...))

        (where/error (σ_1 v_task) (task:allocate σ_0 label))
        (where/error (x_task) (gensyms σ_1 (task)))
        (where/error σ_2 (ext1 σ_1 (x_task v_task)))
        (where/error Q_1 (Q:push Q_0
                                 (x_task
                                  (lambda (none)
                                    (begin none
                                           (reset
                                            (begin
                                              (catch (lambda (v_err) (task:set-failed! x_task v_err))
                                                     (task:set-done! x_task (await v_coro)))
                                              (os/start-soon (task:get-waiters x_task)))))))))
        (where/error t_1 (step t_0))
        "spawn"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (await v_awaitable))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ...
                    (thread (label (in-hole E
                                            (if (task:is-completed? v_awaitable)
                                                (task:get-result v_awaitable)
                                                (shift x_k
                                                       (task:add-waiter! v_awaitable
                                                                         (label
                                                                          (lambda (null)
                                                                            (x_k (task:get-result v_awaitable))))))))) F ...) FS_1 ...))
        (where/error t_1 (step t_0))
        "await-task"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (cancel v_task))) F ...) FS_1 ...))
        (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (task:set-cancelled! v_task))) F ...) FS_1 ...))
        "cancel"]

   [--> (t_0 σ Q T (FS_0 ... (thread (root (in-hole E (block (name v_coro (lambda (x) e))))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ... (thread (root (in-hole E (block (spawn v_coro)))) F ...) FS_1 ...))

        (where/error t_1 (step t_0))
        "block-run"]

   [--> (t_0 σ Q T ((thread (root (in-hole E (block v_task)))) FS ...))
        (t_1 σ Q T ((thread (root (in-hole E (task:get-result v_task)))) FS ...))

        (where #true (task:settled? σ v_task))
        (where/error t_1 (step t_0))
        "block-wait"]

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

(define -->aio
  (union-reduction-relations -->aio/sys -->aio/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "lc.rkt" niceties))

  (define-syntax-rule (aio-->>= e v)
    (test-->> -->aio #:equiv prog/equiv (async/main #:threads 2 e) v))

  (define-syntax-rule (aio-->>∈ e results)
    (evaluates-in-set -->aio (async/main #:threads 2 e) results
                      #:extract-result program-output))

  (define-metafunction AsyncIO
    resume! : e e -> e
    [(resume! e_coro e_val)
     (e_coro e_val)]))

;; Tests that do not use spawn
(module+ test
  (aio-->>=
   (let ([w (async/lambda (x)
              (await (os/io 0 42)))])
     (block (w 0)))
   42))

#;
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
       (block c)))
   "A")

  (aio-->>=
   (let* ([work (async/lambda ()
                  (await (os/io 1 42)))])
     (block (work)))
   42)

  (aio-->>=
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))])
     (block (work)))
   42)

  (aio-->>=
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))]
          [main (async/lambda () (await (spawn (work))))])
     (block (main)))
   42)

  (aio-->>=
   (let* ([exn (async/lambda ()
                 (throw "whoops"))]
          [main (async/lambda ()
                  (begin (spawn (exn))
                         (await (os/io 5 42))))])
     (catch (lambda (e) e)
            (block (main))))
   "whoops")

  (aio-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda () (print "A"))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (block (transparent))))
   "B")

  (aio-->>∈
   (let* ([work (async/lambda () (await (os/io 20 0)))]
          [main (async/lambda ()
                  (let ([t (spawn (work))])
                    (cancel t)))])
     (catch (lambda (e) "cancelled")
            (block (main))))
   '("cancelled" 0))

  (aio-->>∈
   (let* ([work (async/lambda ()
                  (catch (lambda (e) 42)
                         (await (os/io 10 0))))]
          [t (spawn (work))]
          [main (async/lambda ()
                  (begin (cancel t)
                         (await t)))])
     (block (main)))
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
       (block (main))))
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
       (block (main))))
   ; 'C' must *always* come before 'A'
   (filter (lambda (s) (before s #\C #\A))
           (string-permutations "ABC"))))
