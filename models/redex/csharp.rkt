#lang racket

(require redex
         "lc+exn.rkt")

(define-extended-language C# LC+Exn
  (e ::= ....
     (async/lambda (x_!_ ...) e)
     (await e)
     (run e)
     (delay e e)
     (resolve-at e e e))
  
  (v ::= ....
     (async/lambda (x_!_ ...) e)
     (task addr))
  
  (E ::= ....
     (await E)
     (run E)
     (delay v ... E e ...)
     (resolve-at v ... E e ...))

  (l ::= ....
     addr)

  (task-state ::=
              (running (F ...))
              (done v)
              (failed v))
  
  (obj ::= ....
       task-state)

  (Q ::= (F ...))

  #:binding-forms
  
  (async/lambda (x ...) e #:refers-to (shadow x ...)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->c#
  (extend-reduction-relation
   -->except
   C#

   [--> (t_0 H (F_waiting F_s ...) (FS_0 ... (stack) FS_1 ...))
        (t_1 H (F_s ...) (FS_0 ... (stack F_waiting) FS_1 ...))

        (side-condition (term (all-busy? FS_0 ...)))
        (where t_1 (step t_0))
        "idle-thread-work-steal"]

   [--> (t_0 H_0 Q (FS_0 ... (stack (frame L_0 (in-hole E ((async/lambda (x ..._1) e) v ..._1)) l) F ...)
                   FS_1 ...))
        (t_1 H_1 Q (FS_0 ... (stack (frame L_1 e addr) (frame L_0 (in-hole E (task addr)) l) F ...)
                   FS_1 ...))
        
        (where addr (malloc H_0))
        (where L_1 (ext L_0 (x v) ...))
        (where H_1 (ext1 H_0 (addr (running ()))))
        (where t_1 (step t_0))
        "async-app"]

   [--> (t_0 H_0 Q (FS_0 ... (stack (name current-frame
                                          (frame L (in-hole E (await (task addr))) l)) F ...)
                    FS_1 ...))
        (t_1 H_1 Q (FS_0 ... (stack F ...) FS_1 ...))

        (where (running (F_wait ...)) (lookup H_0 addr))
        (where H_1 (ext1 H_0 (addr (running (current-frame F_wait ...)))))
        (where t_1 (step t_0))
        "await"]

   [--> (t_0 H_0 (F_queued ...) (FS_0 ... (stack (frame L v l) F ...) FS_1 ...))
        (t_1 H_1 (F_queued ... F_waiting ...) (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where addr l)
        (where/error (running (F_waiting ...)) (lookup H_0 addr))
        (where H_1 (ext1 H_0 (addr (done v))))
        (where t_1 (step t_0))
        "async-return"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (await (task addr))) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E v) l) F ...) FS_1 ...))
        
        (where (done v) (lookup H addr))
        (where t_1 (step t_0))
        "await-continue"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (await (task addr))) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E (throw v)) l) F ...) FS_1 ...))
        
        (where (failed v) (lookup H addr))
        (where t_1 (step t_0))
        "await-failed"]

   [--> (t_0 H_0 (F_queued ...) (FS_0 ... (stack (frame L (in-hole E (throw v_err)) l) F ...) FS_1 ...))
        (t_1 H_1 (F_queued ... F_waiting ...) (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (side-condition (not (term (in-handler?/c# E))))
        (where addr l)
        (where/error (running (F_waiting ...)) (lookup H_0 addr))
        (where H_1 (ext1 H_0 (addr (failed v_err))))
        (where t_1 (step t_0))
        "async-throw"]

   ;; Simulate IO operations

   [--> (t_0 H_0 (F_queued ...) (FS_0 ... (stack (frame L (in-hole E (delay natural v)) l) F ...) FS_1 ...))
        (t_1 H_1 (F_queued ... (frame L (resolve-at (task addr) (Σ t_0 natural) v) addr))
             (FS_0 ... (stack (frame L (in-hole E (task addr)) l) F ...) FS_1 ...))

        (where addr (malloc H_0))
        (where H_1 (ext1 H_0 (addr (running ()))))
        (where t_1 (step t_0))
        "delay"]
   
   [--> (t_0 H_0 (F_queued ...)
             (FS_0 ... (stack (frame L (in-hole E (resolve-at (task addr) t_resolve v)) l) F ...)
                   FS_1 ...))
        (t_1 H_1 (F_queued ... F_waiting ...) (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (>= (term t_0) (term t_resolve)))
        (where/error (running (F_waiting ...)) (lookup H_0 addr))
        (where H_1 (ext1 H_0 (addr (done v))))
        (where t_1 (step t_0))
        "resolve-at"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (resolve-at v_task t_resolve v)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E (resolve-at v_task t_resolve v)) l) F ...) FS_1 ...))

        (side-condition (< (term t_0) (term t_resolve)))
        (where t_1 (step t_0))
        "resolve-at-blocking"]))

;; -----------------------------------------------------------------------------
;; Metafunctions
;; -----------------------------------------------------------------------------

(define (sync? t)
  (eq? t 'sync))

(define (async? t)
  (not (sync? t)))

(define-metafunction/extension in-handler? C#
    in-handler?/c# : E -> boolean)

(define-metafunction C#
  all-busy? : FS ... -> boolean
  [(all-busy?) #true]
  [(all-busy? (stack) _ ...) #false]
  [(all-busy? (stack _ _ ...) FS_s ...)
   (all-busy? FS_s ...)])

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "lc+exn.rkt" test))
  
  (define-metafunction/extension main/exn C#
    main/c# : e -> (t H Q P)
    [(main/c# e) (0 () () ((stack (frame () (substitute e) sync))
                           (stack)
                           #;(stack)
                           #;(stack)))])
  
  (define-syntax-rule (c#-->>= e v)
    (test-->> -->c# #:equiv prog/equiv (term (main/c# e)) v))

  (define-syntax-rule (c#-->>E e v)
    (test-->>E #:steps 75 -->c# (term (main/c# e)) (lambda (p)
                                                     #;(printf "Program: ~a\n" p)
                                                     (prog/equiv p v))))

(stepper -->c# (term (main/c# (trace-stdout (print)
                 (let* ([work (async/lambda (msg) (print (await (delay 2 msg))))]
                        [task0 (work "A")]
                        [task1 (work "B")])
                   (begin (print "C")
                          (await task0)
                          (await task1)))))))
  
  (c#-->>=
   (await ((async/lambda () 42)))
   42)

  (c#-->>=
   (await ((async/lambda (x) x) 42))
   42)

  (c#-->>=
   (let* ([yield (async/lambda () (void))]
          [id (async/lambda (x)
                            (begin
                              (await (yield))
                              x))])
     
     (await (id 42)))
   42)

  (c#-->>=
   (let* ([mk-t1 (async/lambda () (throw 42))]
          [mk-t2 (async/lambda (x)
                               (catch (lambda (v) v)
                                      (begin
                                        (await (mk-t1))
                                        x)))])
     
     (await (mk-t2 0)))
   42)

  (c#-->>=
   (let ([work (async/lambda () (await (delay 5 42)))])
     (await (work)))
   42)

  (c#-->>E
   (trace-stdout (print)
                 (let* ([work (async/lambda (msg)
                                            (begin
                                              (print (await (delay 2 msg)))
                                              (print (await (delay 2 msg)))))])
                   (await (work "A"))))
   "AA")

  #;
  (c#-->>E
   (trace-stdout (print)
                 (let* ([work (async/lambda (msg) (print (await (delay 2 msg))))]
                        [task0 (work "A")]
                        [task1 (work "B")])
                   (begin (print "C")
                          (await task0)
                          (await task1))))
   "CAB")

  #;
  (c#-->>=
   (trace-stdout (print)
                 (let* ([work (async/lambda (msg)
                                            (begin
                                              (print (await (delay 2 msg)))
                                              (print (await (delay 2 msg)))))]
                        [task0 (work "A")]
                        [task1 (work "B")])
                   (begin (await task0)
                          (await task1))))
  "ABAB"))