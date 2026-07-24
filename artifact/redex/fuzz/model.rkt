#lang racket/base

;; -----------------------------------------------------------------------------
;; Model state: building machine states from surface programs, a canonical
;; dedup key for states, and reading the observable output from a state.
;; Shared by the reference enumerator (reference.rkt) and the directed witness
;; search (witness.rkt), which differ only in how they explore the state graph.
;; -----------------------------------------------------------------------------

(require racket/match
         (only-in racket/list make-list)
         (only-in "../platform.rkt" program-output))

(provide wrap-program
         canonicalize
         canonicalize/timeless
         canon-for-lang
         accumulator-value
         output-so-far
         observed-output
         program-output)

;; ---------------------------------------------------------------------------
;; Wrapping a surface program into a machine state: a `stdout` cell, a `print`
;; that appends to it, a root thread that returns the accumulated string, and
;; `nthreads` empty worker slots for the runtime's thread pool.
;; ---------------------------------------------------------------------------

(define (wrap-for-model e)
  `(let ([stdout ""])
     (let ([print (lambda (s) (set! stdout (string-append stdout s)))])
       (begin ,e stdout))))

(define (wrap-program e nthreads)
  `(0 () () () ((thread (root ,(wrap-for-model e)))
                ,@(make-list nthreads '(thread)))))

;; ---------------------------------------------------------------------------
;; Canonical dedup key: rename heap names by reachability order, drop
;; unreachable store entries, sort the store, and sort T by deadline. T-sort
;; is sound: any pending timer may fire (os/io n = at least n steps), so T's
;; list order never affects reduction -- only the times do.
;; ---------------------------------------------------------------------------

(define (timer-time e) (if (and (pair? e) (real? (car e))) (car e) -inf.0))

(define (canonicalize state)
  (match state
    [(list t σ Q T P)
     (define σ-hash (make-hash))
     (for ([entry (in-list σ)] #:when (pair? entry))
       (hash-set! σ-hash (car entry) (cadr entry)))
     (define renaming (make-hash))
     (define counter 0)
     (define (visit-name! name)
       (when (and (hash-has-key? σ-hash name)
                  (not (hash-has-key? renaming name)))
         (hash-set! renaming name (string->symbol (format "g~a" counter)))
         (set! counter (add1 counter))
         (visit! (hash-ref σ-hash name))))
     (define (visit! x)
       (cond [(symbol? x) (visit-name! x)]
             [(pair? x) (visit! (car x)) (visit! (cdr x))]
             [else (void)]))
     ;; visit T in firing (time) order so the renaming is insertion-order-invariant
     (define T-sorted (sort T < #:key timer-time))
     (visit! P) (visit! Q) (visit! T-sorted)
     (define (rn x)
       (cond [(and (symbol? x) (hash-has-key? renaming x)) (hash-ref renaming x)]
             [(pair? x) (cons (rn (car x)) (rn (cdr x)))]
             [else x]))
     (define σ* (sort (for/list ([(name canon) (in-hash renaming)])
                        (list canon (rn (hash-ref σ-hash name))))
                      symbol<? #:key car))
     (list t σ* (rn Q) (rn T-sorted) (rn P))]
    [_ state]))

;; Timeless key: `canonicalize`, then clock and deadlines zeroed. Sound only
;; because (a) every model's fused sys/signal delivers any pending timer
;; regardless of the clock, and (b) generated programs never observe os/time.
;; If either changes, move the language back to `canonicalize` (canon-for-lang).
(define (zero-timer e)
  (if (and (pair? e) (real? (car e))) (cons 0 (cdr e)) e))

(define (canonicalize/timeless state)
  (match (canonicalize state)
    [(list _t σ Q T P) (list 0 σ Q (map zero-timer T) P)]
    [c c]))

(define (canon-for-lang lang)
  (if (memq lang '(asyncio trio javascript tokio smol swift csharp))
      canonicalize/timeless
      canonicalize))

;; ---------------------------------------------------------------------------
;; Observable output: locate the print accumulator cell by its closure shape
;; and read the output SO FAR (printing only appends, so it is a prefix of the
;; final output). `accumulator-value` is #f when there is no such cell;
;; `output-so-far` normalizes that to "".
;; ---------------------------------------------------------------------------

(define (accumulator-name σ)
  (for/or ([entry (in-list σ)] #:when (pair? entry))
    (match (cadr entry)
      [(list 'lambda (list p)
             (list 'set! (? symbol? x) (list 'string-append x2 p2)))
       (and (eq? x x2) (eq? p p2) x)]
      [_ #f])))

(define (store-ref σ name)
  (for/or ([entry (in-list σ)]
           #:when (and (pair? entry) (equal? (car entry) name)))
    (cadr entry)))

(define (accumulator-value state)
  (match state
    [(list _t σ _Q _T _P)
     (define name (accumulator-name σ))
     (and name (store-ref σ name))]
    [_ #f]))

(define (output-so-far state)
  (or (accumulator-value state) ""))

;; Observed output of a terminal state: everything printed once every thread
;; finished (the process's stdout at exit). The root's return value is only a
;; snapshot at the root's last step -- a mid-poll worker's tail print (probed:
;; real tokio) lands after that read. Root value fallback when no accumulator.
(define (observed-output state)
  (define acc (accumulator-value state))
  (if (string? acc) acc (program-output state)))
