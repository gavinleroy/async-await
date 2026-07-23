#lang racket

(require "../test-utils.rkt")

;; ================================================================
;; Figure 6: Suspension (Section 3.1.2)
;; ================================================================
;;
;; async fn work(msg): print(msg)
;; async fn repeat(msg): await work(msg); await work(msg)
;; async fn main():
;;   a = spawn repeat("A")
;;   b = spawn repeat("B")
;;   print("C")
;;   await a; await b
;;
;; NOTE: The paper shows interleaving on a single-threaded event loop.
;; Our thread-pool model produces different (nondeterministic) interleaving.
;; Key difference: static suspension ALWAYS yields at await (even if ready),
;; dynamic suspension continues synchronously when value is ready.
;;
;; Paper expected (single-threaded, eager):
;;   Static (JS):  ABBABC (specific FIFO interleaving)
;;   Dynamic (C#): AABBC  (no yielding on ready values)

(define/async (fig6-work msg)
  (display msg))

(define/async (fig6-repeat msg)
  (await (fig6-work msg))
  (await (fig6-work msg)))

(define/async (fig6-main)
  (define a (spawn (fig6-repeat "A")))
  (define b (spawn (fig6-repeat "B")))
  (display "C")
  (await a)
  (await b))

(displayln "=== Figure 6: Suspension ===")
(displayln "Expected (paper, single-threaded): Static=ABBABC, Dynamic=AABBC")
(displayln "NOTE: Thread-pool model may produce different interleaving")
(newline)

(run-test "Static (JavaScript)" with-javascript fig6-main)
(run-test "Dynamic (C#)" with-csharp fig6-main)
(newline)
