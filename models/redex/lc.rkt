#lang racket

(require redex)

(provide (all-defined-out))

(define-language LC
  (e ::=
     x
     v
     (set! x e)
     (e e ...)               
     (if e e e)
     (fix e)
     (let ([x_!_ e] ...) e)
     (lambda (x_!_ ...) e)
     (struct [x_!_ e] ...)
     (slot x e)
     (box e)
     (unbox e)
     (set-box! e e)

     ;; numeric operators

     (+ e ...)
     (- e ...)
     (num->string e)
     (= e e)
     (< e e)
     (> e e)
     (<= e e)
     (>= e e)
    
     ;; string operators

     (append e e ...))

  (v ::=
     number
     string
     boolean
     addr
     (void)
     (fix v)
     (lambda (x_!_ ...) e)
     (struct [x_!_ v] ...))

  (E ::=
     hole
     (+ v ... E e ...)
     (- v ... E e ...)
     (= v ... E e ...)
     (< v ... E e ...)
     (> v ... E e ...)
     (<= v ... E e ...)
     (>= v ... E e ...)
     (append v ... E e ...)
     (num->string E)
     (v ... E e ...)
     (fix E)
     (set! x E)
     (let ([x_0 v] ... [x E] [x_1 e] ...) e)
     (if E e e)
     (struct [x_0 v] ... [x E] [x_s e] ...)
     (slot x E)
     (box E)
     (unbox E)
     (set-box! E e)
     (set-box! v E))

  (addr ::= (ptr x))

  (σ ::= ((x v) ...))  

  (x ::= variable-not-otherwise-mentioned)
       
  #:binding-forms
  
  (lambda (x ...) e #:refers-to (shadow x ...))
  
  (let ([x e] ...) e_body #:refers-to (shadow x ...)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->lc
  (reduction-relation
   LC
   #:domain (σ e)
   
   [--> (σ (in-hole E x))
        (σ (in-hole E v))
        
        (where v (lookup σ x))
        "var"]
   
   (--> (σ (in-hole E (if #false e_1 e_2)))
        (σ (in-hole E e_2))
        "if-false")
   
   (--> (σ (in-hole E (if v e_1 e_2)))
        (σ (in-hole E e_1))
        
        (side-condition (not (equal? #false (term v))))
        "if-true")
      
   [--> (σ_0 (in-hole E (set! x v)))
        (σ_1 (in-hole E (void)))
        
        (where σ_1 (ext1 σ_0 (x v)))
        "set!"]

   [--> (σ (in-hole E ((fix v_rec) v_arg ...)))
        (σ (in-hole E ((v_rec (fix v_rec)) v_arg ...)))

        (where (lambda (x ...) e) v_rec)
        "fix"]
   
   [--> (σ_0 (in-hole E ((lambda (x ..._1) e) v ..._1)))
        (σ_1 (in-hole E e))
        
        (where σ_1 (ext σ_0 (x v) ...))
        "app"]   
   
   [--> (σ_0 (in-hole E (let ([x v] ...) e_body)))
        (σ_1 (in-hole E e_body))
        
        (where σ_1 (ext σ_0 (x v) ...))
        "let"]

   [--> (σ (in-hole E (slot x_field v_struct)))
        (σ (in-hole E v))
        

        (where/error (struct [x_s v_s] ...) v_struct)
        (where v (lookup ((x_s v_s) ...) x_field))
        "slot"]

   [--> (σ_0 (name prog (in-hole E (box v))))
        (σ_1 (in-hole E (ptr x)))
        
        (where/error (ptr x) (malloc σ_0))
        (where σ_1 (ext1 σ_0 (x v)))
        "box"]

   [--> (σ (in-hole E (unbox v)))
        (σ (in-hole E v_unboxed))

        (where/error (ptr x) v)
        (where/error v_unboxed (lookup σ x))
        "unbox"]

   [--> (σ_0 (in-hole E (set-box! v_ptr v_new)))
        (σ_1 (in-hole E (void)))

        (where/error (ptr x_addr) v_ptr)
        (where σ_1 (ext1 σ_0 (x_addr v_new)))
        "set-box!"]

   ;; Operations
   
   [--> (σ (in-hole E (+ number ...)))
        (σ (in-hole E (Σ number ...)))
        "add"]

   [--> (σ (in-hole E (- number ...)))
        (σ (in-hole E ,(apply - (term (number ...)))))
        "subtract"]

   [--> (σ (in-hole E (num->string number)))
        (σ (in-hole E ,(number->string (term number))))
        "num->string"]

   [--> (σ (in-hole E (= number ...)))
        (σ (in-hole E ,(apply = (term (number ...)))))
        "num="]

   [--> (σ (in-hole E (< number ...)))
        (σ (in-hole E ,(apply < (term (number ...)))))
        "num<"]

   [--> (σ (in-hole E (> number ...)))
        (σ (in-hole E ,(apply > (term (number ...)))))
        "num>"]

   [--> (σ (in-hole E (<= number ...)))
        (σ (in-hole E ,(apply <= (term (number ...)))))
        "num<="]

   [--> (σ (in-hole E (>= number ...)))
        (σ (in-hole E ,(apply >= (term (number ...)))))
        "num>="]

   [--> (σ (in-hole E (append string ...)))
        (σ (in-hole E (^ string ...)))
        "append"]))
   
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
  malloc : ((any any) ...) -> any
  [(malloc any)
   (ptr (gensym any p))])

(define-metafunction REDEX
  Σ : number ... -> number
  [(Σ number ...) ,(apply + (term (number ...)))])

(define-metafunction REDEX
  ^ : string ... -> string
  [(^ string ...) ,(apply string-append (term (string ...)))])

(define-metafunction REDEX
  && : any ... -> any
  [(&&) #true]
  [(&& any_0 any_s ...)
   (if any_0 (and any_s ...) #false)])

(define-metafunction REDEX
  || : any ... -> any
  [(||) #false]
  [(|| any_0 any_s ...)
   (if any_0 #true (or any_s ...))])

(define-metafunction REDEX
  ~ : any -> any
  [(~ any) (if any #false #true)])

(define-metafunction REDEX
  gensyms : any ... -> (variable ...)
  [(gensyms any ...)
   ,(variables-not-in (term (any ...))
                      (map (lambda _ (term g)) (term (any ...))))])

(define-metafunction REDEX
  gensym : any variable -> variable
  [(gensym any variable)
   ,(variable-not-in (term any) (term variable))])

(define-metafunction REDEX
  lookup : ((any any) ...) any -> any or not-found
  [(lookup (any_prefix ... (any any_0) _ ...) any)
   any_0
   (side-condition (not (member (term any) (term (any_prefix ...)))))]
  [(lookup any_store any_el)
   ,(error 'lookup "~e not found in store: ~e" (term any_el) (term any_store))])

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
  while : any any ... -> any
  [(while any_t any_rest ...)
   (letrec ([any_loop (lambda ()
                        (if any_t
                            (begin any_rest ... (any_loop))
                            (void)))])
     (any_loop))
   (where any_loop ,(variable-not-in (term (any_t any_rest ...)) 'loop))])

(define-metafunction REDEX
  while0< : any any ... -> any
  [(while0< any_n any_rest ...)
   (while (< 0 any_n) any_rest ...)])

(define-metafunction REDEX
  trace-stdout : (any_print) any ... -> any
  [(trace-stdout (any_print) any_s ...)
    (let* ([any_stdout ""]
           [any_print (lambda (s)
                        (set! any_stdout (append any_stdout s)))])
      (begin any_s ... any_stdout))
   (where any_stdout (gensym (any_s ...) stdout))])

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (provide final-value prog/equiv main)

  (define-metafunction LC
    main : e -> (σ e)
    [(main e) (() (substitute e))])
  
  (define (final-value p)
    (match p
      [`(,_σ ,v) v]
      [_ p]))
  
  (define (prog/equiv p v)
    ((default-equiv)
     (final-value p)
     v))
  
  (define-syntax-rule (lc-->>= e v)
    (test-->> -->lc #:equiv prog/equiv (term (main e)) v))
  
  (lc-->>=
   (+ 21 21)
   42)

  (lc-->>=
   (- 42 0)
   42)

  (lc-->>=
   (- 42 42)
   0)

  (lc-->>=
   (- 42 42 42)
   -42)

  (lc-->>=
   (if (= 0 0) 42 21)
   42)
  
  (lc-->>=
   (let ([counter 42] [times 0])
     (begin
       (while (< 0 counter)
              (set! counter (- counter 1))
              (set! times (+ times 1)))
       times))
   42)
   
  (lc-->>=
   ((lambda (x) x) 42)
   42)
     
  (lc-->>=
   (let* ([x 21]
          [y (+ x 10)]
          [z (+ y 11)])
     z)
   42)

  (lc-->>=
   (let ([x 0] [y 42])
     (let ([y x] [x y])
       x))
   42)
   
  (lc-->>=
   (let* ([x 42]
          [c 0]
          [loop (fix (lambda (loop)
                       (lambda ()
                         (if (= 0 x)
                             (void)
                             (begin
                               (set! c (+ c 1))
                               (set! x (+ x -1))
                               (loop))))))])
     (begin (loop) c))
   42)

  (lc-->>=
   (let* ([x 42]
          [c 0])
     (letrec ([loop (lambda ()
                      (if (= 0 x)
                          (void)
                          (begin
                            (set! c (+ c 1))
                            (set! x (+ x -1))
                            (loop))))])
       (begin (loop) c)))
   42)
   
  (lc-->>=
   (let* ([x 42]
          [foo (lambda (x) (set! x 100))])
     (begin (foo x) x))
   42)

  (lc-->>=
   (let* ([x 0]
          [x (begin (set! x 1) (+ x 1))]
          [x (+ x 1)]
          [x (+ x 39)])
     x)
   42)

  (lc-->>=
   (append (num->string 4) (num->string 2))
   "42")

  (lc-->>= 
   (let* ([x 10] [c ""])
     (letrec ([loop (lambda ()
                      (if (= 0 x)
                          (void)
                          (begin
                            (set! x (+ x -1))
                            (set! c (append c (num->string  x)))
                            (loop))))])
       (begin (loop) c)))
   "9876543210")

  (lc-->>= 
   (let* ([x 10] [c (box "")])
     (letrec ([loop (lambda ()
                      (if (= 0 x)
                          (void)
                          (begin
                            (set! x (+ x -1))
                            (set-box! c (append (unbox c) (num->string  x)))
                            (loop))))])
       (begin (loop) (unbox c))))
   "9876543210")

  (lc-->>=
   (slot x (struct [x 42] [y 0]))
   42)

  (lc-->>=
   (let ([s (struct [x (- 42 21)] [y 21])])
     (+ (slot x s)
        (slot y s)))
   42)

  (lc-->>=
   (trace-stdout (print)
                 (print "hello")
                 (print ", world"))
   "hello, world"))