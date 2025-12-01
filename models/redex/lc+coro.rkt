#lang racket

(require redex "lc.rkt")

(provide (all-from-out "lc.rkt")
         (all-defined-out))

(define-extended-language LC+Coro LC
  (e ::= ....              
     (coro e)
     (tagged x e)
     (resume! e e ...)
     (yield e))

  (v ::= ....
     (tag x)
     (coroutine v))
  
  (E ::= ....
     (coro E)
     (tagged x E)
     (resume! v ... E e ...)
     (yield E)
     ))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->coro
  (extend-reduction-relation
   -->sync LC+Coro
   
   [--> (t_0 H Q (FS_0 ... (stack (frame L_0 (in-hole E (coro v)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L_1 (in-hole E (tag x_tag)) l) F ...) FS_1 ...))

        (where x_tag (fresh-tag L_0))
        (where L_1 (ext1 L_0 (x_tag (coroutine v))))
        (where t_1 (step t_0))
        "create"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L_0 (in-hole E (resume! (tag x_tag) v ..._1)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L_1 (in-hole E (tagged x_tag ((lambda (x ...) e_body) v ...))) l) F ...) FS_1 ...))

        (where/error (coroutine (lambda (x ..._1) e_body)) (lookup L_0 x_tag))
        (where L_1 (ext1 L_0 (x_tag (void)))) ;; remove the binding for x_tag
        (where t_1 (step t_0))
        "resume!"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L_0 (in-hole E (tagged x_tag (in-hole E_inner (yield v)))) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L_1 (in-hole E v) l) F ...) FS_1 ...))

        ;; Asymmetric transfer goes from the inner-most nested coroutine to it's caller
        (side-condition (not (term (in-tag? E_inner))))
        (where L_1 (ext1 L_0 (x_tag (coroutine (lambda (x) (in-hole E_inner x))))))
        (where t_1 (step t_0))
        "yield"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (tagged x_tag v)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E v) l) F ...) FS_1 ...))

        (where t_1 (step t_0))
        "tagged"]))

;; -----------------------------------------------------------------------------
;; Metafunctions
;; -----------------------------------------------------------------------------

(define-metafunction LC+Coro
  fresh-tag : L -> x
  [(fresh-tag ((x_s any_s) ...))
   ,(variable-not-in (term (x_s ...)) 'ctag)])

(define-metafunction LC+Coro
  in-tag? : any -> boolean
  [(in-tag? any)
   ,(not (false? (member (term tagged) (flatten (term any)))))
   (side-condition (list? (term any)))]
  [(in-tag? any) #false])

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------



(module+ test
  (require (submod "lc.rkt" test))
  (provide (all-from-out (submod "lc.rkt" test))
           main/coro)

  (define-metafunction/extension main LC+Coro
    main/coro : e -> (t H Q P)
    )
  
  (define-syntax-rule (coro-->>= e v)
    (test-->> -->coro #:equiv prog/equiv (term (main/coro e)) v))
  
  (coro-->>=
   (let* ([genint-coro (let* ([counter 0]
                              [c (coro (lambda (_)
                                         (while-0!= -1
                                           (set! counter (+ counter 1))
                                           (yield counter))))])
             
                         (lambda ()
                           (resume! c (void))))]
          [genint (let ([c 0])
                    (lambda ()
                      (begin (set! c (+ 1 c))
                             c)))]
          [n 50])
     (letrec ([loop (lambda ()
                      (if0 n
                           42
                           (if0 (- (genint) (genint-coro))
                                (begin (set! n (- n 1))
                                       (loop))
                                0)))])
       (loop)))
   42)
  
  (coro-->>=
   (let* ([genint (let* ([counter 0]
                         [c (coro (lambda (_)
                                    (letrec ([loop (lambda ()
                                                     (begin
                                                       (set! counter (+ counter 1))
                                                       (yield counter)
                                                       (loop)))])
                               
                                      (loop))))])
             
                    (lambda ()
                      (resume! c (void))))]
          [gensym
           (lambda ()
             (append "gsym" (num->string (genint))))])
     (begin (gensym)
            (gensym)
            (gensym)))
   "gsym3")
  
  (coro-->>=
   (let* ([fib-gen (let ([a 0] [b 1])
                     (letrec ([loop (lambda ()
                                      (let ([old-a a])
                                        (begin (yield a)
                                               (set! a b)
                                               (set! b (+ old-a b))
                                               (loop))))])
                                  
                       (coro (lambda (_) (loop)))))]
          [next (lambda () (resume! fib-gen (void)))]
          [n-th-fib (lambda (n)
                      (let ([curr (void)])
                        (letrec ([loop (lambda ()
                                         (begin
                                           (set! curr (next))
                                           (if0 n
                                                curr
                                                (begin (set! n (+ n -1))
                                                       (loop)))))])
                          (loop))))])
     (n-th-fib 12))
   144))