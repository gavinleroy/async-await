#lang racket

(require "../pseudo.rkt"
         (for-syntax racket/base))

(provide (except-out (all-from-out racket) #%module-begin)
         (except-out (all-from-out "../pseudo.rkt") is-cancelled?)
         (rename-out [lang-module-begin #%module-begin]))

(define-syntax-rule (lang-module-begin form ...)
  (#%module-begin
   (splicing-with-csharp form ...)))
