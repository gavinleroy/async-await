#lang racket

(require redex/reduction-semantics
         (for-syntax racket/syntax)
         (for-syntax syntax/parse)
         (for-syntax racket/base))

(define-language LC
  (e ::=
     (e e)
     (lambda (x) e)
     x
     number
     (+ e ...))
  (x ::= variable-not-otherwise-mentioned))

(define-syntax (make-language stx)
  (syntax-case stx ()
    [(_ Lang main)
     #'(begin
         (define-syntax (main stx)
           (syntax-parse stx
             [(_ n:nat e)
              (define nums (for/list ([i (in-range (syntax-e #'n))]) i))
              #`(term-let ([(nums (... (... ...))) '#,nums])
                          (term (+ (substitute e) nums (... (... ...)))
                                #:lang Lang))])))]))

(make-language LC main)

(main 4 ((lambda (i) 0) 10))