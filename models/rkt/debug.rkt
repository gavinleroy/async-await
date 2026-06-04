#lang racket

(require "test-utils.rkt")

;; Test 1: simplest possible — no io, no await
(define/async (test1)
  (display "HELLO"))

(displayln "=== Test 1: no await ===")
(run-test "tokio" with-tokio test1)

;; Test 2: await another async fn
(define/async (inner)
  (display "INNER"))

(define/async (test2)
  (await (inner)))

(displayln "=== Test 2: await async fn ===")
(run-test "tokio" with-tokio test2)

;; Test 3: io/delay alone
(define/async (test3)
  (display "A")
  (await (io/delay 50))
  (display "B"))

(displayln "=== Test 3: io/delay ===")
(run-test "tokio" with-tokio test3)
