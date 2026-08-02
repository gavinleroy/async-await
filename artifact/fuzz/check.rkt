#lang racket/base

(require rackunit
         racket/format
         racket/match
         racket/string
         "run.rkt"
         "../redex/typecheck.rkt")

(provide check-runtime-output
         check-runtime-in-set)

;; Compiled programs drop `trace-stdout`: the body's prints go to real stdout
;; (what the check compares), and the program's value becomes "".
(define (strip-trace-stdout e)
  (match e
    [`(trace-stdout (,_print) ,es ...) `(begin ,@es "")]
    [_ e]))

;; Check that compiling and running `e` produces stdout in `expected-vals`.
;; `#:rust?` selects the JoinHandle->Result typing discipline (tokio/smol).
(define (check-runtime-in-set compile-and-run e expected-vals
                              #:normalize [normalize ~a]
                              #:rust? [rust? #f])
  (define-values (typed-e _type) (type-check (strip-trace-stdout e) #:rust? rust?))
  (cond
    [(not typed-e)
     (fail (format "type-check failed: ~s" e))]
    [else
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
         (format "stdout ~s not in ~s" stdout expected-strs))])]))

;; Single-value convenience wrapper.
(define (check-runtime-output compile-and-run e expected-val
                              #:normalize [normalize ~a]
                              #:rust? [rust? #f])
  (check-runtime-in-set compile-and-run e (list expected-val)
                        #:normalize normalize #:rust? rust?))
