#lang racket

(provide (all-defined-out))

(define (now)
  (current-inexact-milliseconds))

(define (elapsed-ms start)
  (truncate (- (now) start)))
