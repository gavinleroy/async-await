#lang racket

(provide (all-defined-out))

(define-syntax-rule (log forms ...)
  (begin (eprintf forms ...) (eprintf "\n")))
