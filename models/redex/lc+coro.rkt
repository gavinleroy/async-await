#lang racket

(require redex "lc.rkt")

(provide LC+Coro -->coro/core -->coro in-tag? tag?)

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
     (yield E)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->coro/core
  (reduction-relation
   LC+Coro #:domain (H L e)

   [--> (H L_0 (in-hole E (coro v)))
        (H L_1 (in-hole E (tag x_tag)))

        (where x_tag (gensym L_0 ctag))
        (where L_1 (ext1 L_0 (x_tag (coroutine v))))
        "create"]

   [--> (H L_0 (in-hole E (resume! (tag x_tag) v ..._1)))
        (H L_1 (in-hole E (tagged x_tag ((lambda (x ...) e_body) v ...))))

        (where/error (coroutine (lambda (x ..._1) e_body)) (lookup L_0 x_tag))
        (where L_1 (ext1 L_0 (x_tag (void)))) ;; remove the binding for x_tag
        "resume!"]

   [--> (H L_0 (in-hole E (tagged x_tag (in-hole E_inner (yield v)))))
        (H L_1 (in-hole E v))

        ;; Asymmetric transfer goes from the inner-most nested coroutine to it's caller
        (side-condition (not (term (in-tag? E_inner))))
        (where L_1 (ext1 L_0 (x_tag (coroutine (lambda (x) (in-hole E_inner x))))))
        "yield"]

   [--> (H L (in-hole E (tagged x_tag v)))
        (H L (in-hole E v))
        "tagged"]))

(define -->lc/base
  (extend-reduction-relation -->lc LC+Coro))

(define -->coro
  (union-reduction-relations -->lc/base -->coro/core))

;; -----------------------------------------------------------------------------
;; Metafunctions
;; -----------------------------------------------------------------------------

(define-metafunction LC+Coro
  in-tag? : any -> boolean
  [(in-tag? any)
   ,(not (false? (member (term tagged) (flatten (term any)))))
   (side-condition (list? (term any)))]
  [(in-tag? any) #false])

(define (tag? t)
  (match t
    [`(tag ,_) #true]
    [_ #false]))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "lc.rkt" test))
  (provide main/coro)

  (define-metafunction/extension main LC+Coro
    main/coro : e -> (H L e))
  
  (define-syntax-rule (coro-->>= e v)
    (test-->> -->coro #:equiv prog/equiv (term (main/coro e)) v))

  (coro-->>=
   (let ([c (coro (lambda (x)
                     (begin (yield (+ x 1))
                            (yield (+ x 2))
                            (+ x 3))))])
     (let ([a (resume! c 0)]
           [b (resume! c 0)]
           [c (resume! c 0)])
       (+ a b c)))
   6)

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
          [make
           (lambda ()
             (append "gsym" (num->string (genint))))])
     (begin (make)
            (make)
            (make)))
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