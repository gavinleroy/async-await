#lang racket/base

(require rackunit
         racket/format
         racket/match
         racket/string
         "run.rkt"
         "../typecheck.rkt")

(provide check-runtime-output
         check-runtime-in-set)

;; `trace-stdout` goes away in compiled programs: the body's `(print ...)`
;; forms write to the process's real stdout, which is what the check compares
;; against. The program's value becomes "" so the runtime's final result
;; print contributes nothing after trimming.
(define (strip-trace-stdout e)
  (match e
    [`(trace-stdout (,_print) ,es ...) `(begin ,@es "")]
    [_ e]))

;; Check that compiling and running `e` produces stdout
;; matching one of `expected-vals`.
;; `#:rust?` selects the JoinHandle→Result typing discipline (tokio/smol),
;; under which awaiting a spawned task yields a Result struct.
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
