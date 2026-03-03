#lang racket

(require redex
         "lc.rkt"
         (prefix-in lib: (submod "lc.rkt" niceties))
         "lc+exn.rkt"
         "lc+coro.rkt"
         "python.rkt"
         "platform.rkt")

(provide AsyncIO/Core AsyncIO -->aio)

(define-extended-language AsyncIO/Core Python

  (e ::= ....
     (spawn e)
     (cancel e)
     (run e))
  
  (v ::= ....
     (task x_async))
  
  (E ::= ....
     (spawn E)
     (cancel E)
     (run E)))

(define-event-loop
  AsyncIO AsyncIO/Core)

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->base
  (extend-reduction-relation -->py AsyncIO))


(define -->aio/sync
  (reduction-relation
   AsyncIO #:domain (t σ Q P)

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame e_0 l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame e_1 l) F ...) FS_1 ...))

        (side-condition (not (term (value? e))))
        (where (σ_1 e_1) (⇓base σ_0 e_0))
        (where t_1 (step t_0))
        "⇓base"]))


(define -->aio/task
  (reduction-relation
   AsyncIO #:domain (t σ Q P)

   [--> (t_0 σ_0 Q_0 (FS_0 ... (stack (frame (in-hole E (spawn (tag x_label))) l) F ...) FS_1 ...))
        (t_1 σ_1 Q_1 (FS_0 ... (stack (frame (in-hole E (task x_async)) l) F ...) FS_1 ...))

        (where/error (ptr x_async) (malloc σ_0))
        (where/error σ_1 (ext1 σ_0 (x_async (new-task (tag x_label)))))
        (where/error Q_1 (q-push Q_0 (frame (resume! (tag x_label) (void)) x_async)))
        (where/error t_1 (step t_0))
        "task-spawn"]

   
   [--> (t_0 σ_0 Q_0 (FS_0 ... (stack (frame (in-hole E (run v)) l) F ...) FS_1 ...))
        (t_1 σ_1 Q_1 (FS_0 ... (stack (frame (in-hole E (task x_async)) l) F ...) FS_1 ...))

        (where/error (lambda () e) v)
        (where (ptr x_async) (malloc σ_0))
        (where/error σ_1 (ext1 σ_0 (x_async (new-task))))
        (where/error Q_1 (q-push Q_0 (frame e x_async)))
        (where/error t_1 (step t_0))
        "task-run"]

   [--> (t_0 σ_0 Q_0 (FS_0 ... (stack (frame v l) F ...) FS_1 ...))
        (t_1 σ_1 Q_1 (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where x_async l)
        (where v_obj (lookup σ_0 x_async))
        (where/error (pending F_waiting ...) (task-state v_obj))
        (where/error σ_1 (ext1 σ_0 (x_async (task-settle v_obj v))))
        (where/error Q_1 (q-push Q_0 F_waiting ...))
        (where/error t_1 (step t_0))
        "task-return"]

   [--> (t_0 σ_0 Q_0 (FS_0 ... (stack (frame (throw v) l) F ...) FS_1 ...))
        (t_1 σ_1 Q_1 (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where x_async l)
        (where v_obj (lookup σ_0 x_async))
        (where/error (pending (frame (resume! (tag x_pending) _) l_waiting) ...)
                     (task-state v_obj))
        (where/error σ_1 (ext1 σ_0 (x_async (task-fail v_obj v))))
        (where/error Q_1 (q-push Q_0 (frame (throw-in! (tag x_pending) v) l_waiting) ...))
        (where/error t_1 (step t_0))
        "task-failed"]))


(define -->aio/await
  (reduction-relation
   AsyncIO #:domain (t σ Q P)

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame
                                     (in-hole E (tagged x_running (in-hole J (await (task x_async))))) l)
                                    F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack F ...) FS_1 ...))

        (where (pending _ ...) (task-state (lookup σ_0 x_async)))        
        (where/error x_awaited (gensym σ_0 dummy))
        (where/error σ_1 (ext σ_0
                              (x_running (coroutine
                                          (lambda (x_awaited)
                                            (in-hole J x_awaited))))
                              (x_async (task-push-waiting
                                        (lookup σ_0 x_async)
                                        (frame (resume! (tag x_running)
                                                        (slot value x_async)) l)))))
        (where/error t_1 (step t_0))
        "await-suspend"]
   
   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame (in-hole E (await (task x_async))) l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame (in-hole E v) l) F ...) FS_1 ...))

        (where/error v_obj (lookup σ_0 x_async))
        (where (done v) (task-state v_obj))
        (where/error σ_1 (ext1 σ_0 (x_async (task-awaited v_obj))))
        (where/error t_1 (step t_0))
        "await-continue"]

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame (in-hole E (await (task x_async))) l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame (in-hole E (throw v)) l) F ...) FS_1 ...))

        (where v_obj (lookup σ_0 x_async))
        (where (failed v) (task-state v_obj))
        (where/error σ_1 (ext1 σ_0 (x_async (task-awaited v_obj))))
        (where/error t_1 (step t_0))
        "await-failed"]))


(define -->aio/cancel
  (reduction-relation
   AsyncIO #:domain (t σ Q P)

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame (in-hole E (cancel (task x_async))) l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame (in-hole E (void)) l) F ...) FS_1 ...))

        (where v_obj (lookup σ_0 x_async))
        (where/error σ_1 (ext1 σ_0 (x_async (task-cancel v_obj))))
        (where/error t_1 (step t_0))
        "cancel"]

   [--> (t_0 σ Q_0 (FS_main FS_0 ... (stack) FS_1 ...))
        (t_1 σ Q_1 (FS_main FS_0 ... (stack (frame (throw-in! (tag x_tag) "cancelled") x_async)) FS_1 ...))

        (where ((frame (resume! (tag x_tag) _) x_async) Q_1) (q-pop Q_0))
        (side-condition (term (task-cancelled? (lookup σ x_async))))
        (side-condition (term (all-busy? FS_0 ...)))
        (where t_1 (step t_0))
        "dequeue-cancelled"]))


(define -->aio/io
  (reduction-relation
   AsyncIO #:domain (t σ Q P)

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame (in-hole E (os/io natural v)) l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame (in-hole E (spawn (tag x_tag))) l) F ...) FS_1 ...))
        
        (where (x_dummy x_tag) (lib:gensyms σ_0 σ_0))
        (where σ_1 (ext1 σ_0 (x_tag (coroutine (lambda (x_dummy)
                                                 (begin x_dummy
                                                        (lib:while (<= (os/time) (lib:Σ t_0 natural))
                                                                   (yield (tag x_tag)))
                                                        v))))))
        (where/error t_1 (step t_0))
        "os/io"]

   [--> (t_0 σ Q (FS_0 ... (stack (frame (in-hole E (os/time)) l) F ...) FS_1 ...))
        (t_1 σ Q (FS_0 ... (stack (frame (in-hole E t_0) l) F ...) FS_1 ...))
        
        (where/error t_1 (step t_0))
        "os/time"]))


(define -->aio/sys
  (reduction-relation
   AsyncIO #:domain (t σ Q P)

   [--> (t_0 σ Q_0 (FS_main FS_0 ... (stack) FS_1 ...))
        (t_1 σ Q_1 (FS_main FS_0 ... (stack next-frame) FS_1 ...))

        (where ((name next-frame (frame _ x_async)) Q_1) (q-pop Q_0))
        (side-condition (not (term (task-cancelled? (lookup σ x_async)))))
        (side-condition (term (all-busy? FS_0 ...)))
        (where t_1 (step t_0))
        "dequeue"]
   
   [--> (t_0 σ Q ((stack (frame (in-hole E (block (tag x_coro))) l)) FS_1 ...))
        (t_1 σ Q ((stack (frame (in-hole E (block (spawn (tag x_coro)))) l)) FS_1 ...))

        (side-condition (sync? (term l)))
        (where/error t_1 (step t_0))
        "block"]

   [--> (t_0 σ () ((stack (frame (in-hole E (block (task x_async))) l)) FS_rest ...))
        (t_1 σ () ((stack (frame (in-hole E v) l)) FS_rest ...))

        (side-condition (sync? (term l)))
        (side-condition (not (term (any-busy? FS_rest ...))))
        (where (done v) (task-state (lookup σ x_async)))
        (where none (find-unawaited-error σ))
        (where/error t_1 (step t_0))
        "block-exit"]

   [--> (t_0 σ () ((stack (frame (in-hole E (block (task x_async))) l)) FS_rest ...))
        (t_1 σ () ((stack (frame (in-hole E (throw v)) l)) FS_rest ...))

        (side-condition (sync? (term l)))
        (side-condition (not (term (any-busy? FS_rest ...))))
        (where (some v) (find-unawaited-error σ))
        (where/error t_1 (step t_0))
        "block-fail"]))


(define -->aio
  (union-reduction-relations
   -->aio/sync
   -->aio/task
   -->aio/await
   -->aio/cancel
   -->aio/io
   -->aio/sys))


(define-big-step ⇓base
  -->base AsyncIO)

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require "utils.rkt"
           (submod "lc.rkt" niceties))
  
  (define-syntax-rule (aio-->>= e v)
    (test-->> -->aio #:equiv prog/equiv (async/main #:threads 2 e) v))

  (define-syntax-rule (aio-->>∈ e results)
    (evaluates-in-set -->aio (async/main #:threads 2 e) results
                      #:extract-result program-output))

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