#lang racket

(require "../test-utils.rkt"
         (only-in rackunit check-equal?))

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

(define/async (ex1)
  (await (process-detach)))

(define/async (ex2)
  (define task (spawn (process-await)))
  (await (io/delay 100))
  (cancel task))

(define/async (ex3)
  (define task (spawn (process-detach)))
  (await (io/delay 100))
  (cancel task))

;; Zero-arg entry points — `block` requires an identifier
(define/async (entry-ex1)
  (await (io/delay 3000 (await (ex1)))))

(define/async (entry-ex2)
  (await (io/delay 3000 (await (ex2)))))

(define/async (entry-ex3)
  (await (io/delay 3000 (await (ex3)))))

(define-syntax run-example
  (syntax-rules ()
    [(_ with-lang entry)
     (let ([port (open-output-string)])
       (with-handlers ([exn? (lambda (e) #f)])
         (parameterize ([current-output-port port])
           (with-lang (block entry))))
       (get-output-string port))]))

(define-syntax test-one
  (syntax-rules ()
    [(_ with-lang entry expected)
     (let ([exp expected])
       (when exp
         (check-equal? (run-example with-lang entry) exp
                       (format "~a/~a" 'with-lang 'entry))))]))

;; #f = skip (no cancel support in that language)
(define-syntax test-figure
  (syntax-rules ()
    [(_ (entry-a entry-b entry-c)
        [with-lang exp-a exp-b exp-c] ...)
     (begin
       (begin (test-one with-lang entry-a exp-a)
              (test-one with-lang entry-b exp-b)
              (test-one with-lang entry-c exp-c))
       ...)]))

(test-figure (entry-ex1 entry-ex2 entry-ex3)
;;                 ex1   ex2   ex3
  [with-tokio      "AB"  "AB"  "AB"]
  [with-smol       "A"   ""    ""  ]
  [with-asyncio    "AB"  ""    "AB"]
  [with-trio       "AB"  "A"   "AB"]
  [with-csharp     "A"   #f    #f  ]
  [with-javascript "AB"  #f    #f  ]
  [with-swift      "A"   "A"   "A" ])
