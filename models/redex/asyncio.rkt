#lang racket

(require redex
         "utils.rkt"
         "lc.rkt"
         "lc+exn.rkt"
         "lc+coro.rkt"
         "python.rkt")

(define-extended-language AsyncIO Python

  (e ::= ....
     (spawn e)
     (cancel e)
     (run e)
     (delay e e)
     (resolve-at e e e))
  
  (v ::= ....
     (task addr v ...))
  
  (E ::= ....
     (spawn E)
     (cancel E)
     (run E)
     (delay E e)
     (delay v E)
     (resolve-at E e e)
     (resolve-at v E e)
     (resolve-at v v E))

  (task-state ::=
              (running v ... F ...)
              (done v)
              (failed v))

  (obj ::= ....
       task-state)

  (t ::= natural)
  
  (l ::= sync addr)
  
  (F ::= (frame L e l))
  
  (Q ::= (F ...))

  (FS ::= (stack F ...))
  
  (P ::= (FS ...)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->base
  (extend-reduction-relation -->py AsyncIO))

(define -->aio
  (reduction-relation
   AsyncIO #:domain (t H Q P)

   [--> (t_0 H_0 (F_s ...)
             (FS_0 ... (stack (frame L (in-hole E (run v)) l) F ...) FS_1 ...))
        (t_1 H_1 ((frame L e addr) F_s ...)
             (FS_0 ... (stack (stack (frame L (in-hole E (task addr)) l) F ...)) FS_1 ...))

        (where/error (lambda () e) v)
        (where addr (malloc H_0))
        (where H_1 (ext1 H_0 (addr (running))))
        (where t_1 (step t_0))
        "task-run"]

   [--> (t_0 H_0 (F_queued ...) (FS_0 ... (stack (frame L (in-hole E (spawn v_coro)) l) F ...) FS_1 ...))
        (t_1 H_1 (F_queued ...
                  (frame L (resume! v_coro (void)) addr))
             (FS_0 ... (stack (frame L (in-hole E (task addr v_coro)) l) F ...) FS_1 ...))

        (where/error (tag x_label) v_coro)
        (where addr (malloc H_0))
        (where H_1 (ext1 H_0 (addr (running v_coro))))
        (where t_1 (step t_0))
        "spawn"]

   [--> (t_0 H (F_queued ...) (FS_0 ... (stack (frame L (tag x_label) l) F ...) FS_1 ...))
        (t H (F_queued ... (frame L (resume! (tag x_label) (void))))
           (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where addr l)
        (where (running (tag x_label) F_waiting ...) (lookup H addr))
        (where t_1 (step t_0))
        "task-reschedule"]

   [--> (t_0 H_0 (F_queued ...) (FS_0 ... (stack (frame L v l) F ...) FS_1 ...))
        (t_1 H_1 (F_queued ... F_waiting ...) (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where addr l)
        (where/error (running v_coro ... F_waiting ...) (lookup H_0 addr))
        (side-condition (not (member (term v) (term (v_coro ...)))))
        (where H_1 (ext1 H_0 (addr (done v))))
        (where t_1 (step t_0))
        "task-return"]

   [--> (t_0 H_0 Q (FS_0 ... (stack (name current-frame (frame L (in-hole E (await (task addr))) l)) F ...) FS_1 ...))
        (t_1 H_1 Q (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where (running F_waiting ...) (lookup H_0 addr))
        (where H_1 (ext1 H_0 (addr (running current-frame F_waiting ...))))
        (where t_1 (step t_0))
        "task-await-pending"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (await (task addr _ ...))) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E v) l) F ...) FS_1 ...))
        
        (where (done v) (lookup H addr))
        (where t_1 (step t_0))
        "task-await-done"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (await (task addr _))) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E (throw v)) l) F ...) FS_1 ...))
        
        (where (failed v) (lookup H addr))
        (where t_1 (step t_0))
        "task-await-failed"]

   [--> (t_0 H_0 (F_queued ...) (FS_0 ... (stack (frame L (in-hole E (throw v_err)) l) F ...) FS_1 ...))
        (t_1 H_1 (F_queued ... F_waiting ...) (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (side-condition (not (term (in-handler?/aio E))))
        (where addr l)
        (where/error (running F_waiting ...) (lookup H_0 addr))
        (where H_1 (ext1 H_0 (addr (failed v_err))))
        (where t_1 (step t_0))
        "async-throw"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (cancel v)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E (throw-in v_coro "cancelled")) l) F ...) FS_1 ...))

        (where/error (task addr v_coro) v)
        (where/error t_1 (step t_0))
        "cancel"]
   
   [--> (t_0 H_0 (F_queued ...) (FS_0 ... (stack (frame L (in-hole E (delay natural v)) l) F ...) FS_1 ...))
        (t_1 H_1 (F_queued ... (frame L (resolve-at (task addr) (Σ t_0 natural) v) addr))
             (FS_0 ... (stack (frame L (in-hole E (task addr)) l) F ...) FS_1 ...))

        (where/error addr (malloc H_0))
        (where/error H_1 (ext1 H_0 (addr (running))))
        (where/error t_1 (step t_0))
        "delay"]

   [--> (t_0 H_0 (F_queued ...)
             (FS_0 ... (stack (frame L (in-hole E (resolve-at (task addr) t_resolve v)) l) F ...)
                   FS_1 ...))
        (t_1 H_1 (F_queued ... F_waiting ...) (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (>= (term t_0) (term t_resolve)))
        (where/error (running F_waiting ...) (lookup H_0 addr))
        (where H_1 (ext1 H_0 (addr (done v))))
        (where t_1 (step t_0))
        "resolve-at"]

   [--> (t_0 H (F_queued ...)
             (FS_0 ... (stack (name current-frame
                                    (frame L (in-hole E (resolve-at v_task t_resolve v)) l)) F ...)
              FS_1 ...))
        (t_1 H (F_queued ... current-frame)
             (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (< (term t_0) (term t_resolve)))
        (where t_1 (step t_0))
        "resolve-at-blocking"]

   [--> (t_0 H (F_waiting F_s ...) (FS_main FS_0 ... (stack F ...) FS_1 ...))
        (t_1 H (F_s ...) (FS_main FS_0 ... (stack F_waiting F ...) FS_1 ...))

        (side-condition (term (all-busy? FS_0 ...)))
        (where t_1 (step t_0))
        "thread-work-steal"]
   
   [--> (t_0 H_0 Q (FS_0 ... (stack (frame L_0 e_0 l) F ...) FS_1 ...))
        (t_1 H_1 Q (FS_0 ... (stack (frame L_1 e_1 l) F ...) FS_1 ...))

        (side-condition (not (value? (term e))))
        (where (H_1 L_1 e_1) (⇓base H_0 L_0 e_0))
        (where t_1 (step t_0))
        "base-step"]

   ))

;; -----------------------------------------------------------------------------
;; Metafunctions
;; -----------------------------------------------------------------------------

(define-metafunction/extension in-handler? AsyncIO
    in-handler?/aio : E -> boolean)

(define-metafunction/extension awaitable? AsyncIO
  awaitable?/aio : v -> boolean
  [(awaitable?/aio (task _ ...)) #true])

(define-metafunction AsyncIO
  all-busy? : FS ... -> boolean
  [(all-busy?) #true]
  [(all-busy? (stack) _ ...) #false]
  [(all-busy? (stack _ _ ...) FS_s ...)
   (all-busy? FS_s ...)])

(define (value? t)
  (redex-match? AsyncIO v t))

(define-big-step ⇓base
  -->base AsyncIO)

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test

  (define-metafunction AsyncIO
    main/aio : e -> (t H Q P)
    [(main/aio e) (0 () () ((stack (frame () (substitute e) sync))
                            (stack)
                            #;(stack)))])

  (define (final-value p)
    (match p
      [`(,_t ,_H ,_Q ((stack (frame ,_L ,v ,_l)) ,_ ...)) v]
      [_ p]))
  
  (define (prog/equiv p v)
    ((default-equiv)
     (final-value p)
     v))
  
  (define-syntax-rule (aio-->>= e v)
    (test-->> -->aio #:equiv prog/equiv (term (main/aio e)) v))

  (define-syntax-rule (aio-->>E e v)
    (test-->>E #:steps 40 -->aio (term (main/aio e)) (lambda (p)
                                                       (prog/equiv p v))))

  #;
  (stepper -->aio
           (term (main/aio
                  (trace-stdout (print)
                 (let* ([work (async/lambda (msg)
                                            (print (await (delay 1 msg))))]
                        [main (async/lambda ()
                                            (let ([t1 (spawn (work "A"))])
                                              (await t1)))])
                   (block (main)))))))
  
  (aio-->>=
   (block ((async/lambda (x) 42) 0))
   42)

  (aio-->>= 
   (trace-stdout (print)
                 (let* ([suspend (async/lambda () (void))]
                        [main (async/lambda (msg)
                                            (begin (await (suspend))
                                                   (print msg)
                                                   (await (suspend))
                                                   (print msg)
                                                   (await (suspend))
                                                   (print msg)))])
                   (block (main "A"))))
   "AAA")

  (aio-->>=
   (trace-stdout (print)
                 (let* ([append-it (async/lambda () (print "A"))]
                        [transparent (async/lambda ()
                                                   (let ([ret (append-it)])
                                                     (begin (print "B") ret)))])
                   (block (block (transparent)))))
   "BA")
  
  (aio-->>= 
   (trace-stdout (print)
                 (let* ([suspend (async/lambda () (void))]
                        [work (async/lambda (msg)
                                            (begin (await (suspend))
                                                   (print msg)))]
                        [main (async/lambda ()
                                            (let ([task0 (work "A")]
                                                  [task1 (work "B")])
                                              (begin
                                                (print "C")
                                                (await task0)
                                                (await task1))))])
                   (block (main))))
   "CAB")

  (aio-->>=
   (trace-stdout (print)
                 (let ([work (async/lambda ()
                                           (print (await (delay 1 "A"))))])
                   (block (work))))
   "A")
  
  (aio-->>= 
   (trace-stdout (print)
                 (let* ([work (async/lambda (msg)
                                            (print (await (delay 1 msg))))]
                        [main (async/lambda ()
                                            (let ([t1 (work "A")]
                                                  [t2 (work "B")])
                                              (begin (print "C")
                                                     (await t1)
                                                     (await t2))))])
                   (block (main))))
   "CAB")

  (aio-->>E 
   (trace-stdout (print)
                 (let* ([work (async/lambda (msg)
                                            (print (await (delay 1 msg))))]
                        [main (async/lambda ()
                                            (let ([t1 (work "A")]
                                                  [t2 (spawn (work "B"))])
                                              (begin (print "C")
                                                     (await t1)
                                                     (await t2))))])
                   (block (main))))
   "CBA")

  
  (aio-->>=
   (let* ([work (async/lambda ()
                              (catch (lambda (e) 42)
                                     (await (delay 20 42))))]
          [t (spawn (work))])
     (begin (cancel t)
            (await t)))
   42))