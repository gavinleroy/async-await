#lang racket

(require "test-utils.rkt")

;; ================================================================
;; Figure 1: Motivating Example (Section 1)
;; ================================================================
;;
;; Programs:
;;   write_to_log():  print("A"); await sleep(2); print("B")
;;   process_detach(): spawn write_to_log()
;;   process_await():  task = spawn write_to_log(); await task
;;   ex1(): await process_detach()
;;   ex2(): task = spawn process_await(); await sleep(1); task.cancel()
;;   ex3(): task = spawn process_detach(); await sleep(1); task.cancel()
;;
;; Expected outcomes (Figure 1c), L = no output:
;;              ex1   ex2   ex3
;;   Tokio      AB    AB    AB
;;   Smol       A     L     L
;;   Asyncio    AB    L     AB
;;   Trio       AB    A     AB
;;   C#         A     -     -
;;   JavaScript AB    -     -
;;   Swift      A     A     A

(define/async (write-to-log)
  (display "A")
  (await (io/delay 200))
  (display "B"))

(define/async (process-detach)
  (spawn (write-to-log)))

(define/async (process-await)
  (define task (spawn (write-to-log)))
  (await task))

(define/async (fig1-ex1)
  (await (process-detach)))

(define/async (fig1-ex2)
  (define task (spawn (process-await)))
  (await (io/delay 100))
  (cancel task))

(define/async (fig1-ex3)
  (define task (spawn (process-detach)))
  (await (io/delay 100))
  (cancel task))

(displayln "=== Figure 1: Motivating Example ===")
(displayln "Expected: Tokio(AB,AB,AB) Smol(A,L,L) Asyncio(AB,L,AB)")
(displayln "          Trio(AB,A,AB) C#(A) JS(AB) Swift(A,A,A)")
(newline)

(displayln "Tokio (lazy, indefinite, strong, cancelled, unaware, top-down):")
(run-test "ex1" with-tokio fig1-ex1)
(run-test "ex2" with-tokio fig1-ex2)
(run-test "ex3" with-tokio fig1-ex3)
(newline)

(displayln "Smol (lazy, indefinite, weak, cancelled, unaware, top-down):")
(run-test "ex1" with-smol fig1-ex1)
(run-test "ex2" with-smol fig1-ex2)
(run-test "ex3" with-smol fig1-ex3)
(newline)

(displayln "Asyncio (lazy, indefinite, weak, cancelled, aware, bottom-up, transient):")
(run-test "ex1" with-asyncio fig1-ex1)
(run-test "ex2" with-asyncio fig1-ex2)
(run-test "ex3" with-asyncio fig1-ex3)
(newline)

(displayln "Trio (lazy, dynamic, strong, awaited, destruction-prop, aware, bottom-up, persistent):")
(run-test "ex1" with-trio fig1-ex1)
(run-test "ex2" with-trio fig1-ex2)
(run-test "ex3" with-trio fig1-ex3)
(newline)

(displayln "C# (eager, dynamic-susp, indefinite, strong, terminated, unaware):")
(run-test "ex1" with-csharp fig1-ex1)
(displayln "  ex2: - (no built-in cancel)")
(displayln "  ex3: - (no built-in cancel)")
(newline)

(displayln "JavaScript (eager, static-susp, indefinite, strong, awaited, unaware):")
(run-test "ex1" with-javascript fig1-ex1)
(displayln "  ex2: - (no built-in cancel)")
(displayln "  ex3: - (no built-in cancel)")
(newline)

(displayln "Swift (semi-eager, dynamic-susp, dynamic, strong, cancelled, aware, simultaneous, persistent):")
(run-test "ex1" with-swift fig1-ex1)
(run-test "ex2" with-swift fig1-ex2)
(run-test "ex3" with-swift fig1-ex3)
(newline)

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

;; ================================================================
;; Figure 9: Propagation (Section 3.2.4)
;; ================================================================
;;
;; async def fail(): raise Exception()
;; async def main():
;;   print("A")
;;   nursery.spawn(fail)   <-- in Trio, nursery awaits children
;;   print("B")
;;
;; NOTE: Our model doesn't have nursery scopes. With dynamic extent
;; + awaited destruction, the parent waits for children at task
;; settlement (after body completes), so "B" is printed before
;; the error propagates. In real Trio, the nursery blocks inline
;; and "B" is never reached.
;;
;; Expected (real Trio):      "A"  — nursery re-raises fail's exception
;; Expected (never-prop):     "AB" — exception ignored
;; Expected (our model, Trio): "AB" then error propagated

(define/async (fig9-fail)
  (raise (make-exn:fail "task failure" (current-continuation-marks))))

(define/async (fig9-main)
  (display "A")
  (spawn (fig9-fail))
  (display "B"))

(displayln "=== Figure 9: Propagation ===")
(displayln "Expected (real Trio): A-only. Expected (never): AB")
(displayln "NOTE: Our model lacks nursery scopes; see comment in source")
(newline)

(run-test "Destruction propagation (Trio)" with-trio fig9-main)
(run-test "Never propagation (C#)" with-csharp fig9-main)
(newline)

;; ================================================================
;; Figure 10: Awareness (Section 3.3.1)
;; ================================================================
;;
;; async fn work():
;;   break_invariant()
;;   try:
;;     await process()
;;   finally:
;;     restore_invariant()
;;
;; t = spawn work(); t.cancel()
;;
;; Expected:
;;   Aware (Python/Swift): "BREAK RESTORE" — finally block runs
;;   Unaware (Rust):       "BREAK"         — task killed, no cleanup

;; NOTE: We use with-handlers (not dynamic-wind) because Racket's
;; dynamic-wind interacts with delimited continuations: abort/cc at
;; the await point crosses the wind boundary, triggering cleanup
;; prematurely. with-handlers correctly models Python's try/except.
(define/async (fig10-work)
  (display "BREAK ")
  (with-handlers ([exn:cancelled?
                   (lambda (e) (display "RESTORE ") (raise e))])
    (await (io/delay 100)))
  (display "DONE "))

(define/async (fig10-main)
  (define t (spawn (fig10-work)))
  (await (io/delay 50))
  (cancel t))

(displayln "=== Figure 10: Awareness ===")
(displayln "Expected: Aware=BREAK RESTORE, Unaware=BREAK")
(newline)

(run-test* "Aware (eager, dynamic, cancelled, aware, bottom-up, persistent)"
  ([*eagerness* 'eager] [*suspension* 'dynamic]
   [*extent* 'dynamic] [*ref-strength* 'strong]
   [*destruction* 'cancelled] [*propagation* 'never]
   [*awareness* 'aware] [*direction* 'bottom-up]
   [*persistence* 'persistent])
  fig10-main)

(run-test* "Unaware (eager, dynamic, cancelled, unaware, top-down, transient)"
  ([*eagerness* 'eager] [*suspension* 'dynamic]
   [*extent* 'dynamic] [*ref-strength* 'strong]
   [*destruction* 'cancelled] [*propagation* 'never]
   [*awareness* 'unaware] [*direction* 'top-down]
   [*persistence* 'transient])
  fig10-main)
(newline)

(displayln "=== Done ===")
