#lang racket

(require redex)

(provide (all-defined-out))

(define (before s a b)
  (for/fold ([p1 0]
             [p2 0]
             #:result (< p1 p2))
            ([char (in-string s)]
             [i (in-naturals)]
             #:when (or (char=? char a) (char=? char b)))
    (if (char=? char a)
        (values i p2)
        (values p1 i))))

(define (string-permutations s)
  (map list->string
       (permutations (string->list s))))
