#lang racket

(require "timing.rkt"
         "csharp.rkt")

(define/async (func1 a b)
  (define start (now))
  (define v1 (await (delay 1000 a)))
  (define v2 (await (delay 1000 b)))
  (define result (+ v1 v2))
  (printf "took ~ams\n" (elapsed-ms start))
  result)

(define/async (func2 a b)
  (define start (now))
  (define v1 (delay 1000 a))
  (define v2 (delay 1000 b))
  (define result (+ (await v1) (await v2)))
  (printf "took ~ams\n" (elapsed-ms start))
  result)

(define/async (func3)
  (printf "wait for it ...\n")
  (await (delay 1000))
  (raise "boom!"))

(define/async (true) #t)

(define/async (unyielding msg)
  (displayln msg)
  (when (await (true))
    (await (unyielding msg))))

(define/async (main)
  (define c1 (unyielding "C1"))
  (define c2 (unyielding "C2"))
  (await c1)
  (await c2))

(parameterize ([*pool-size* 1])
  (async-run-entry main))
