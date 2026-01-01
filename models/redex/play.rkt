#lang racket

(require redex/reduction-semantics
         (for-syntax racket/syntax))

(define-language LC
  (e ::=
     (e e)
     (lambda (x) e)
     x
     number
     (+ e ...))
  (x ::= variable-not-otherwise-mentioned))

(begin-for-syntax
  (define-syntax-rule (with-unhygenic srcloc (name ...) body)
    (with-syntax ([name (datum->syntax srcloc 'name srcloc)] ...)
      body)))

(define-syntax (deflang stx)
  (syntax-case stx ()
    [(_ name)
     (with-unhygenic #'name (lambda?)
       #'(begin
         (define-extended-language name LC)

         (define (lambda? t)
           (redex-match? name (lambda (x) e) t))))]))

(deflang Foo)

(lambda? (term (lambda (x) (+ x 1))))