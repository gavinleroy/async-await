#lang racket

(require redex/reduction-semantics "lc.rkt")

(provide (all-defined-out))

(define-metafunction REDEX
  q-pop : (any ...) -> (any (any ...)) or empty
  [(q-pop ()) empty]
  [(q-pop (any any_s ...))
   (any (any_s ...))])

(define-metafunction REDEX
  q-push : (any ...) any ... -> (any ...)
  [(q-push (any_s ...) any_el ...)
   (any_s ... any_el ...)])

(define-metafunction REDEX
  all-busy? : any ... -> boolean
  [(all-busy?) #true]
  [(all-busy? (stack) _ ...) #false]
  [(all-busy? (stack _ _ ...) any_s ...)
   (all-busy? any_s ...)])

(define-metafunction REDEX
  any-busy? : any ... -> boolean
  [(any-busy?) #false]
  [(any-busy? (stack _ _ ...) any_s ...)
   #true]
  [(any-busy? (stack) any_rest ...) (any-busy? any_rest ...)])

(define (sync? t)
  (eq? t 'sync))

(define (async? t)
  (not (sync? t)))

(define-syntax-rule (define-big-step bs ss lang)
  (define-metafunction lang
    bs : σ e -> (σ e) or stuck
    [(bs σ_0 e_0)
     (σ_1 e_1)
     (where ((σ_1 e_1)) 
            ,(apply-reduction-relation*
              ss (term (σ_0 e_0))
              #:error-on-multiple? #true))
     (side-condition (not (equal? (term e_0) (term e_1))))]
    [(⇓base _ _) stuck]))

(define-syntax (define-event-loop stx)
  (syntax-case stx ()
    ((_ Lang Base)
     #'(define-extended-language Lang Base
         (e ::= ....
            (block e)
            (os/time)
            (os/io e e)
            (os/resolve e e e))

         (E ::= ....
            (block E)
            (os/io E e)
            (os/io v E)
            (os/resolve E e e)
            (os/resolve v E e)
            (os/resolve v v E))

         (v ::= ....
            (kont F (... ...)))
  
         (t ::= natural)
  
         (l ::= sync x)
  
         (F ::= (frame e l))
  
         (Q ::= (F (... ...)))

         (FS ::= (stack F (... ...)))
  
         (P ::= (FS (... ...)))))))

;; TODO, I can't figure out the binding scopes ...
#;(begin
           
    (define-metafunction Lang
      q-pop : Q -> (F Q) or empty
      [(q-pop ()) empty]
      [(q-pop (F F_s (... ...)))
       (F (F_s (... ...)))])

    (define-metafunction Lang
      q-push : Q F (... ...) -> Q
      [(q-push (F_s (... ...)) F_el (... ...))
       (F_s (... ...) F_el (... ...))])

    (define-metafunction Lang
      all-busy? : FS (... ...) -> boolean
      [(all-busy?) #true]
      [(all-busy? (stack) _ (... ...)) #false]
      [(all-busy? (stack _ _ (... ...)) FS_s (... ...))
       (all-busy? FS_s (... ...))])

    (define-metafunction Lang
      any-busy? : FS (... ...) -> boolean
      [(any-busy?) #false]
      [(any-busy? (stack _ _ (... ...)) FS_s (... ...))
       #true]
      [(any-busy? (stack) FS_rest (... ...)) (any-busy? FS_rest (... ...))])

    (define-metafunction Lang
      value? : any -> boolean
      [(value? v) #true]
      [(value? any) #false]))