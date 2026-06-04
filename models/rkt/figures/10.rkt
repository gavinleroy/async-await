#lang racket

(require "../test-utils.rkt")

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
