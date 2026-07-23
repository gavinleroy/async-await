#lang racket

;; redex/reduction-semantics (not the full `redex`, which pulls in redex/gui →
;; framework → GTK and fails to load on a headless display).
(require redex/reduction-semantics)

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
