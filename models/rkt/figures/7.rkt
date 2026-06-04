#lang racket

(require "../test-utils.rkt")

;; ================================================================
;; Figure 7: Extent (Section 3.2.1)
;; ================================================================
;;
;; async fn work(): await sleep(10); print("B")
;; async fn main(): spawn work(); print("A")
;;
;; Expected:
;;   Dynamic (Swift): "A"  — work cancelled when main scope ends
;;   Indefinite (JS): "AB" — work outlives main, completes

(define/async (fig7-work)
  (await (io/delay 200))
  (display "B"))

(define/async (fig7-main)
  (spawn (fig7-work))
  (display "A"))

(displayln "=== Figure 7: Extent ===")
(displayln "Expected: Dynamic=A, Indefinite=AB")
(newline)

(run-test "Dynamic extent (Swift)" with-swift fig7-main)
(run-test "Indefinite extent (JavaScript)" with-javascript fig7-main)
(newline)
