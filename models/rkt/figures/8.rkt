#lang racket

(require "../test-utils.rkt")

;; ================================================================
;; Figure 8: Destruction (Section 3.2.3)
;; ================================================================
;;
;; async fn work():
;;   await sleep(10); print("A")
;;   await sleep(10); print("B")
;; async fn main():
;;   t = spawn work()
;;   await sleep(15)
;;
;; Tests dynamic extent with varying destruction.
;; main completes between work's two prints.
;;
;; Expected:
;;   Awaited:    "AB" — waits for work to finish
;;   Cancelled:  "A"  — work cancelled at second sleep
;;   Terminated: "A"  — work killed at second sleep

(define/async (fig8-work)
  (await (io/delay 100))
  (display "A")
  (await (io/delay 100))
  (display "B"))

(define/async (fig8-main)
  (spawn (fig8-work))
  (await (io/delay 150)))

(displayln "=== Figure 8: Destruction ===")
(displayln "Expected: Awaited=AB, Cancelled=A, Terminated=A")
(newline)

(run-test* "Awaited"
  ([*eagerness* 'eager] [*suspension* 'dynamic]
   [*extent* 'dynamic] [*ref-strength* 'strong]
   [*destruction* 'awaited] [*propagation* 'never]
   [*awareness* 'unaware] [*direction* 'top-down]
   [*persistence* 'transient])
  fig8-main)

(run-test* "Cancelled"
  ([*eagerness* 'eager] [*suspension* 'dynamic]
   [*extent* 'dynamic] [*ref-strength* 'strong]
   [*destruction* 'cancelled] [*propagation* 'never]
   [*awareness* 'unaware] [*direction* 'top-down]
   [*persistence* 'transient])
  fig8-main)

(run-test* "Terminated"
  ([*eagerness* 'eager] [*suspension* 'dynamic]
   [*extent* 'dynamic] [*ref-strength* 'strong]
   [*destruction* 'terminated] [*propagation* 'never]
   [*awareness* 'unaware] [*direction* 'top-down]
   [*persistence* 'transient])
  fig8-main)
(newline)
