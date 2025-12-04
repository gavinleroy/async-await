#lang racket

(require redex
         "utils.rkt"
         "lc.rkt"
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
     (delay E e)
     (delay v E)
     (resolve-at E e e)
     (resolve-at v E e)
     (resolve-at v v E))

  (task-state ::=
              (running (F ...))
              (done v)
              (failed v))
  
  (obj ::= ....
       task-state)

  (t ::= natural)
  
  (l ::= sync addr)
  
  (F ::= (frame L e l))
  
  (Q ::= (F ...))

  (FS ::= (stack F ...))
  
  (P ::= (FS ...))

  #:binding-forms
  
  (async/lambda (x ...) e #:refers-to (shadow x ...)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->base
  (extend-reduction-relation -->exn C#))

(define -->c#
  (reduction-relation
   C#
   #:domain (t H Q P)

   [--> (t_0 H_0 (F_s ...)
             (FS_0 ... (stack (frame L (in-hole E (run v)) l) F ...) FS_1 ...))
        (t_1 H_1 ((frame L e addr) F_s ...)
             (FS_0 ... (stack (stack (frame L (in-hole E (task addr)) l) F ...)) FS_1 ...))

        (where/error (lambda () e) v)
        (where addr (malloc H_0))
        (where H_1 (ext1 H_0 (addr (running ()))))
        (where t_1 (step t_0))
        "task-run"]
   
   [--> (t_0 H_0 Q (FS_0 ... (stack (frame L_0 (in-hole E ((async/lambda (x ..._1) e) v ..._1)) l) F ...)
                         FS_1 ...))
        (t_1 H_1 Q (FS_0 ... (stack (frame L_1 e addr) (frame L_0 (in-hole E (task addr)) l) F ...)
                         FS_1 ...))
        
        (where addr (malloc H_0))
        (where L_1 (ext L_0 (x v) ...))
        (where H_1 (ext1 H_0 (addr (running ()))))
        (where t_1 (step t_0))
        "async-app"]

   [--> (t_0 H_0 (F_queued ...) (FS_0 ... (stack (frame L v l) F ...) FS_1 ...))
        (t_1 H_1 (F_queued ... F_waiting ...) (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where addr l)
        (where/error (running (F_waiting ...)) (lookup H_0 addr))
        (where H_1 (ext1 H_0 (addr (done v))))
        (where t_1 (step t_0))
        "task-return"]

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

   [--> (t_0 H_0 Q (FS_0 ... (stack (name current-frame
                                          (frame L (in-hole E (await (task addr))) l)) F ...)
                    FS_1 ...))
        (t_1 H_1 Q (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where (running (F_wait ...)) (lookup H_0 addr))
        (where H_1 (ext1 H_0 (addr (running (current-frame F_wait ...)))))
        (where t_1 (step t_0))
        "await"]

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
        "resolve-at-blocking"]
   
   [--> (t_0 H (F_waiting F_s ...) (FS_main FS_0 ... (stack) FS_1 ...))
        (t_1 H (F_s ...) (FS_main FS_0 ... (stack F_waiting) FS_1 ...))

        (side-condition (term (all-busy? FS_0 ...)))
        (where t_1 (step t_0))
        "thread-work-steal"]

   [--> (t_0 H_0 Q (FS_0 ... (stack (frame L_0 e_0 l) F ...) FS_1 ...))
        (t_1 H_1 Q (FS_0 ... (stack (frame L_1 e_1 l) F ...) FS_1 ...))

        (side-condition (not (value? (term e))))
        (where (H_1 L_1 e_1) (⇓base H_0 L_0 e_0))
        (where t_1 (step t_0))
        "base-step"]))

;; -----------------------------------------------------------------------------
;; Metafunctions
;; -----------------------------------------------------------------------------

(define-metafunction/extension in-handler? C#
    in-handler?/c# : E -> boolean)

(define-metafunction C#
  all-busy? : FS ... -> boolean
  [(all-busy?) #true]
  [(all-busy? (stack) _ ...) #false]
  [(all-busy? (stack _ _ ...) FS_s ...)
   (all-busy? FS_s ...)])

(define (value? t)
  (redex-match? C# v t))

(define-big-step ⇓base
  -->base C#)

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  
  (define-metafunction C#
    main/c# : e -> (t H Q P)
    [(main/c# e) (0 () () ((stack (frame () (substitute e) sync))
                           (stack)
                           (stack)))])

  (define (final-value p)
    (match p
      [`(,_t ,_H ,_Q ((stack (frame ,_L ,v ,_l)) ,_ ...)) v]
      [_ p]))
  
  (define (prog/equiv p v)
    ((default-equiv)
     (final-value p)
     v))
  
  (define-syntax-rule (c#-->>= e v)
    (test-->> -->c# #:equiv prog/equiv (term (main/c# e)) v))

  (define-syntax-rule (c#-->>E e v)
    (test-->>E #:steps 40 -->c# (term (main/c# e)) (lambda (p)
                                                     (prog/equiv p v))))

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

  (c#-->>=
   (trace-stdout (print)
                 (let* ([work (async/lambda (msg)
                                            (begin
                                              (print (await (delay 1 msg)))
                                              (print (await (delay 1 msg)))))])
                   (await (work "A"))))
   "AA")

  (c#-->>E
   (trace-stdout (print)
                 (let* ([work (async/lambda (msg)
                                            (begin (await (delay 1 (void)))
                                                   (print msg)))]
                        [task0 (work "A")]
                        [task1 (work "B")])
                   (begin (print "C")
                          (await task0)
                          (await task1))))
   "CAB")

  (c#-->>E
   (trace-stdout (print)
                 (let* ([work (async/lambda (msg) (print (await (delay 1 msg))))]
                        [task0 (work "A")]
                        [task1 (work "B")])
                   (begin (print "C")
                          (await task0)
                          (await task1))))
   "CBA"))