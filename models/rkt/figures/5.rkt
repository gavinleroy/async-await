#lang racket

(require "../test-utils.rkt")

;; ================================================================
;; Figure 5: Eagerness (Section 3.1.1)
;; ================================================================
;;
;; async fn work(msg): print(msg)
;; async fn main():
;;   a = work("A")
;;   b = work("B")
;;   print("C")
;;   await a
;;   await b
;;
;; Expected:
;;   Lazy (Rust):        "CAB" — work not started until awaited
;;   Eager (C#):         "ABC" — work runs inline when called
;;   Semi-eager (Swift): nondeterministic — work scheduled, interleaves with "C"

(define/async (fig5-work msg)
  (display msg))

(define/async (fig5-main)
  (define a (fig5-work "A"))
  (define b (fig5-work "B"))
  (display "C")
  (await a)
  (await b))

(displayln "=== Figure 5: Eagerness ===")
(displayln "Expected: Lazy=CAB, Eager=ABC, Semi-eager=nondeterministic")
(newline)

(run-test "Lazy (Tokio)" with-tokio fig5-main)
(run-test "Eager (C#)" with-csharp fig5-main)
(run-test "Semi-eager (Swift)" with-swift fig5-main)
(newline)
