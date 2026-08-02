#lang racket/base

;; -----------------------------------------------------------------------------
;; Differential-testing hook. Every model test case reports here; without
;; ASYNC_DIFFERENTIAL these are no-ops and the test suites are pure Redex
;; (safe for machines without the language toolchains, e.g. the package
;; build farm). With ASYNC_DIFFERENTIAL=<fuzz-dir> each term is also
;; compiled and executed on the real runtime via <fuzz-dir>/check.rkt
;; (requires node, python, dotnet, swiftc, and cargo on PATH).
;; -----------------------------------------------------------------------------

(provide differential-output differential-in-set)

(define fuzz-dir (getenv "ASYNC_DIFFERENTIAL"))

(define (fuzz-ref file sym)
  (dynamic-require (build-path fuzz-dir file) sym))

(define check-output (and fuzz-dir (fuzz-ref "check.rkt" 'check-runtime-output)))
(define check-in-set (and fuzz-dir (fuzz-ref "check.rkt" 'check-runtime-in-set)))

;; lane names the compile-and-run-<lane> entry in <fuzz-dir>/run.rkt
(define (runner lane)
  (fuzz-ref "run.rkt" (string->symbol (format "compile-and-run-~a" lane))))

(define (differential-output lane e v #:normalize [normalize #f] #:rust? [rust? #f])
  (when fuzz-dir
    (if normalize
        (check-output (runner lane) e v #:normalize normalize #:rust? rust?)
        (check-output (runner lane) e v #:rust? rust?))))

(define (differential-in-set lane e vs #:normalize [normalize #f] #:rust? [rust? #f])
  (when fuzz-dir
    (if normalize
        (check-in-set (runner lane) e vs #:normalize normalize #:rust? rust?)
        (check-in-set (runner lane) e vs #:rust? rust?))))
