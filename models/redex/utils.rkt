#lang racket

(require redex)

(provide (all-defined-out))

(define (sync? t)
  (eq? t 'sync))

(define (async? t)
  (not (sync? t)))

(define-syntax-rule (define-big-step bs ss lang)
  (define-metafunction lang
    bs : H L e -> (H L e) or stuck
    [(bs H L e_0)
     (H_1 L_1 e_1)
     (where ((H_1 L_1 e_1)) 
            ,(apply-reduction-relation*
              ss (term (H L e_0))
              #:error-on-multiple? #true))
     (side-condition (not (equal? (term e_0) (term e_1))))]
    [(⇓base _ _ _) stuck]))