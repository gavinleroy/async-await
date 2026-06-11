#lang racket/base

(require rackunit
         racket/format
         racket/string
         "run.rkt"
         "../typecheck.rkt")

(provide check-runtime-output
         check-runtime-in-set)

;; Check that compiling and running `e` produces stdout
;; matching one of `expected-vals`.
(define (check-runtime-in-set compile-and-run e expected-vals
                              #:normalize [normalize ~a])
  (define-values (typed-e _type) (type-check e))
  (unless typed-e
    (fail (format "type-check failed: ~s" e)))
  (define r (compile-and-run typed-e))
  (cond
    [(eq? (run-result-exit-code r) 'timeout)
     (fail (format "runtime timed out: ~s" e))]
    [(not (zero? (run-result-exit-code r)))
     (fail (format "runtime crashed (exit ~a): ~s\nstderr: ~a"
                   (run-result-exit-code r) e
                   (string-trim (run-result-stderr r))))]
    [else
     (define stdout (string-trim (run-result-stdout r)))
     (define expected-strs (map normalize expected-vals))
     (check-not-false
      (member stdout expected-strs)
      (format "stdout ~s not in ~s" stdout expected-strs))]))

;; Single-value convenience wrapper.
(define (check-runtime-output compile-and-run e expected-val
                              #:normalize [normalize ~a])
  (check-runtime-in-set compile-and-run e (list expected-val)
                        #:normalize normalize))
