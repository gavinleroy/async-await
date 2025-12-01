#lang racket

(require redex)

(provide (all-defined-out))

(define-language LC
  (e ::=
     x
     v
     (void)
     (set! x e)
     (+ e ...)
     (- e ...)
     (num->string e)
     (append e e ...)
     (time)
     (e e ...)               
     (if0 e e e)
     (fix e)
     (let ([x_!_ e] ...) e)
     (lambda (x_!_ ...) e)
     (struct [x_!_ e] ...)
     (slot x e)
     (box e)
     (unbox e)
     (set-box! e e))

  (v ::=
     number
     string
     (void)
     (fix v)
     (lambda (x_!_ ...) e)
     (struct [x_!_ v] ...)
     (ptr addr))

  (E ::=
     hole
     (+ v ... E e ...)
     (- v ... E e ...)
     (append v ... E e ...)
     (num->string E)
     (v ... E e ...)
     (fix E)
     (set! x E)
     (let ([x_0 v] ... [x E] [x_1 e] ...) e)
     (if0 E e e)
     (struct [x_0 v] ... [x E] [x_s e] ...)
     (slot x E)
     (box E)
     (unbox E)
     (set-box! E e)
     (set-box! v E))

  (t ::= natural)
  
  (L ::= ((x v) ...))
  
  (l ::= sync)
  
  (F ::= (frame L e l))
  
  (FS ::= (stack F ...))

  (addr ::= natural)

  (obj ::= (box v))
  
  (H ::= ((addr obj) ...))

  (Q ::= ())
  
  (P ::= (FS ...))
  
  (x ::= variable-not-otherwise-mentioned)
       
  #:binding-forms
  
  (lambda (x ...) e #:refers-to (shadow x ...))
  
  (let ([x e] ...) e_body #:refers-to (shadow x ...)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->sync
  (reduction-relation
   LC
   #:domain (t H Q P)
   
   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E x) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E (lookup L x)) l) F ...) FS_1 ...))

        (where t_1 (step t_0))
        "var"]
   
   (--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (if0 0 e_1 e_2)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E e_1) l) F ...) FS_1 ...))

        (where t_1 (step t_0))
        "if0-true")
   
   (--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (if0 v e_1 e_2)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E e_2) l) F ...) FS_1 ...))
        
        (side-condition (not (equal? 0 (term v))))
        (where t_1 (step t_0))
        "if0-false")
      
   [--> (t_0 H Q (FS_0 ... (stack (frame L_0 (in-hole E (set! x v)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L_1 (in-hole E (void)) l) F ...) FS_1 ...))
        
        (where L_1 (ext1 L_0 (x v)))
        (where t_1 (step t_0))
        "set!"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L_0
                                   (in-hole E ((fix v_rec) v_arg ...)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L_0
                                   (in-hole E ((v_rec (fix v_rec)) v_arg ...)) l) F ...) FS_1 ...))

        (where t_1 (step t_0))
        "fix"]
   
   [--> (t_0 H Q (FS_0 ... (stack (frame L_0 (in-hole E ((lambda (x ..._1) e) v ..._1)) l) F ...)
                     FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L_1 (in-hole E e) l) F ...) FS_1 ...))
        
        (where L_1 (ext L_0 (x v) ...))
        (where t_1 (step t_0))
        "app"]   
   
   [--> (t_0 H Q (FS_0 ... (stack (frame L_0 (in-hole E (let ([x v] ...) e_body)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L_1 (in-hole E e_body) l) F ...) FS_1 ...))
        
        (where L_1 (ext L_0 (x v) ...))
        (where t_1 (step t_0))
        "let"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (slot x_field v_struct)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E v) l) F ...) FS_1 ...))

        (where/error (struct [x_s v_s] ...) v_struct)
        (where v (lookup ((x_s v_s) ...) x_field))
        (where t_1 (step t_0))
        "slot"]

   [--> (t_0 H_0 Q (FS_0 ... (stack (frame L (in-hole E (box v)) l) F ...) FS_1 ...))
        (t_1 H_1 Q (FS_0 ... (stack (frame L (in-hole E (ptr addr)) l) F ...) FS_1 ...))

        (where addr (malloc H_0))
        (where H_1 (ext1 H_0 (addr (box v))))
        (where t_1 (step t_0))
        "box"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (unbox v)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E v_unboxed) l) F ...) FS_1 ...))

        (where/error (ptr addr) v)
        (where/error (box v_unboxed) (lookup H addr))
        (where t_1 (step t_0))
        "unbox"]

   [--> (t_0 H_0 Q (FS_0 ... (stack (frame L (in-hole E (set-box! v_ptr v_new)) l) F ...) FS_1 ...))
        (t_1 H_1 Q (FS_0 ... (stack (frame L (in-hole E (void)) l) F ...) FS_1 ...))

        (where/error (ptr addr) v_ptr)
        (where/error (box _) (lookup H_0 addr))
        (where H_1 (ext1 H_0 (addr (box v_new))))
        (where t_1 (step t_0))
        "set-box!"]

   ;; Operations
   
   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (+ number ...)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E (Σ number ...)) l) F ...) FS_1 ...))

        (where t_1 (step t_0))
        "add"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (- number ...)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E ,(apply - (term (number ...)))) l) F ...)
                     FS_1 ...))

        (where t_1 (step t_0))
        "subtract"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (append string ...)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E (^ string ...)) l) F ...) FS_1 ...))

        (where t_1 (step t_0))
        "append"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (num->string number)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E ,(number->string (term number))) l) F ...)
                     FS_1 ...))

        (where t_1 (step t_0))
        "num->string"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (time)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E t_0) l) F ...) FS_1 ...))

        (where t_1 (step t_0))
        "time"]))
   
;; -----------------------------------------------------------------------------
;; Metafunctions
;;
;; NOTE, all metafunctions should be defined in terms of the REDEX language. To
;; avoid all of the issues with langauge extensions and metafunctions.
;; -----------------------------------------------------------------------------

(define-language REDEX)

(define-metafunction REDEX
  step : natural -> natural
  [(step natural_0) ,(+ 1 (term natural_0))])

(define-metafunction REDEX
  malloc : ((natural any) ...) -> natural
  [(malloc ()) 0]
  [(malloc ((natural any) ...))
   ,(+ 1 (apply max (term (natural ...))))])

(define-metafunction REDEX
  Σ : number ... -> number
  [(Σ number ...) ,(apply + (term (number ...)))])

(define-metafunction REDEX
  ^ : string ... -> string
  [(^ string ...) ,(apply string-append (term (string ...)))])

(define-metafunction REDEX
  lookup : ((any any) ...) any -> any
  [(lookup (any_prefix ... (any any_0) _ ...) any)
   any_0
   (side-condition (not (member (term any) (term (any_prefix ...)))))]
  [(lookup any_1 any_2)
   ,(error 'lookup "not found: ~e in: ~e" (term any_2) (term any_1))])

(define-metafunction REDEX
  ext1 : ((any any) ...) (any any) -> ((any any) ...)
  [(ext1 (any_0 ... (any_k any_v0) any_1 ...) (any_k any_v1))
   (any_0 ... (any_k any_v1) any_1 ...)]
  [(ext1 (any_0 ...) (any_k any_v1))
   ((any_k any_v1) any_0 ...)])

(define-metafunction REDEX
  ext : ((any any) ...) (any any) ... -> ((any any) ...)
  [(ext any) any]
  [(ext any any_0 any_1 ...)
   (ext1 (ext any any_1 ...) any_0)])          
   
(define-metafunction REDEX
  gensyms : any ... -> (any ...)
  [(gensyms any ...)
   ,(map (lambda _ (term dummy)) (term (any ...)))])

;; We could add these to the base LC, but just for testing 

(define-metafunction REDEX
  let* : ([any any] ...) any -> any
  [(let* () any) any]
  [(let* ([any_x any] [any_x_s any_s] ...) any_body)
   (let ([any_x any]) (let* ([any_x_s any_s] ...) any_body))])

(define-metafunction REDEX
  begin : any ...+ -> any
  [(begin any) any]
  [(begin any_s ... any_body)
   (let ([any_vars any_s] ...) any_body)
   (where (any_vars ...) ,(variables-not-in (term (any_s ...)) (term (gensyms any_s ...))))])

(define-metafunction REDEX
  letrec : ([any any] ...) any -> any
  [(letrec ([any_x (lambda (any_x_args ...) any_fbody)] ...) any_body)
   (let ([any_x (fix (lambda (any_x) (lambda (any_x_args ...) any_fbody)))] ...)
     any_body)])

(define-metafunction REDEX
  while-0!= : any any ... -> any
  [(while-0!= any_n any_rest ...)
   (letrec ([any_loop (lambda ()
                        (if0 any_n
                             (void)
                             (begin any_rest ... (any_loop))))])
     (any_loop))
   (where any_loop ,(variable-not-in (term (any_n any_rest ...)) 'loop))])

(define-metafunction REDEX
  trace-stdout : (any_print) any ... -> any
  [(trace-stdout (any_print) any_s ...)
    (let* ([any_stdout (box "")]
           [any_print (lambda (s)
                        (set-box! any_stdout (append (unbox any_stdout) s)))])
      (begin any_s ... (unbox any_stdout)))
   (where any_stdout ,(variable-not-in (term any) 'stdout))])

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (provide final-value prog/equiv main)

  (define-metafunction LC
    main : e -> (t H Q P)
    [(main e) (0 () () ((stack (frame () (substitute e) sync))))])
  
  (define (final-value h+p)
    (match h+p
      [`(,_t ,_H ,_Q ((stack (frame ,_L ,v ,_l)) ,_FS ...))
       v]
      [_ h+p]))
  
  (define (prog/equiv p v)
    ((default-equiv)
     (final-value p)
     v))
  
  (define-syntax-rule (sync-->>= e v)
    (test-->> -->sync #:equiv prog/equiv (term (main e)) v))
  
  (sync-->>=
   (+ 21 21)
   42)

  (sync-->>=
    (- 42 0)
    42)

  (sync-->>=
    (- 42 42)
    0)

  (sync-->>=
    (- 42 42 42)
    -42)
  
  (sync-->>=
   (let ([counter 42] [times 0])
     (begin
       (while-0!= counter
                  (set! counter (- counter 1))
                  (set! times (+ times 1)))
       times))
   42)
   
  (sync-->>=
   ((lambda (x) x) 42)
   42)
     
  (sync-->>=
   (let* ([x 21]
          [y (+ x 10)]
          [z (+ y 11)])
     z)
   42)

  (sync-->>=
   (let ([x 0] [y 42])
     (let ([y x] [x y])
       x))
   42)
   
  (sync-->>=
   (let* ([x 42]
          [c 0]
          [loop (fix (lambda (loop)
                       (lambda ()
                         (if0 x
                              (void)
                              (begin
                                (set! c (+ c 1))
                                (set! x (+ x -1))
                                (loop))))))])
     (begin (loop) c))
   42)

  (sync-->>=
   (let* ([x 42]
          [c 0])
     (letrec ([loop (lambda ()
                      (if0 x
                           (void)
                           (begin
                             (set! c (+ c 1))
                             (set! x (+ x -1))
                             (loop))))])
       (begin (loop) c)))
   42)
   
  (sync-->>=
   (let* ([x 42]
          [foo (lambda (x) (set! x 100))])
     (begin (foo x) x))
   42)

  (sync-->>=
   (let* ([x 0]
          [x (begin (set! x 1) (+ x 1))]
          [x (+ x 1)]
          [x (+ x 39)])
     x)
   42)

  (sync-->>=
   (append (num->string 4) (num->string 2))
   "42")

  (sync-->>= 
   (let* ([x 10] [c ""])
     (letrec ([loop (lambda ()
                      (if0 x
                           (void)
                           (begin
                             (set! x (+ x -1))
                             (set! c (append c (num->string  x)))
                             (loop))))])
       (begin (loop) c)))
   "9876543210")

  (sync-->>= 
   (let* ([x 10] [c (box "")])
     (letrec ([loop (lambda ()
                      (if0 x
                           (void)
                           (begin
                             (set! x (+ x -1))
                             (set-box! c (append (unbox c) (num->string  x)))
                             (loop))))])
       (begin (loop) (unbox c))))
   "9876543210")

  (sync-->>=
   (slot x (struct [x 42] [y 0]))
  42)

  (sync-->>=
   (let ([s (struct [x (- 42 21)] [y 21])])
     (+ (slot x s)
        (slot y s)))
   42)

  (sync-->>=
   (trace-stdout (print)
     (print "hello")
     (print ", world"))
   "hello, world"))