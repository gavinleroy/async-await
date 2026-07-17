#lang racket/base

;; -----------------------------------------------------------------------------
;; Model state: building machine states from surface programs, a canonical
;; dedup key for states, and reading the observable output from a state.
;;
;; This is the layer shared by the two model-output strategies — the sound
;; reference enumerator (reference.rkt) and the directed witness search
;; (witness.rkt).
;; They differ only in HOW they explore the reachable state graph, never in how
;; a state is constructed, compared, or observed; that common ground lives here.
;; -----------------------------------------------------------------------------

(require racket/match
         (only-in racket/list make-list)
         (only-in "../platform.rkt" program-output))

(provide wrap-program
         canonicalize
         accumulator-value
         output-so-far
         observed-output
         program-output)

;; ---------------------------------------------------------------------------
;; Wrapping a surface program into a machine state
;;
;; The enumerators work on raw surface programs (no `trace-stdout`), so we wrap
;; the program to capture its printed output: a single `stdout` cell, a `print`
;; that appends to it, and a root thread that finally returns the accumulated
;; string. `nthreads` empty worker slots model the runtime's thread pool.
;; ---------------------------------------------------------------------------

(define (wrap-for-model e)
  `(let ([stdout ""])
     (let ([print (lambda (s) (set! stdout (string-append stdout s)))])
       (begin ,e stdout))))

(define (wrap-program e nthreads)
  `(0 () () () ((thread (root ,(wrap-for-model e)))
                ,@(make-list nthreads '(thread)))))

;; ---------------------------------------------------------------------------
;; Canonical dedup key: rename heap names by reachability order from the control
;; state, drop unreachable store entries, sort the store, and order the timer
;; queue T by deadline.
;;
;; T-sort: a timer entry is `(time task thunk)`. `sys/signal` may fire ANY due
;; timer and `os/block-wait` may jump the clock to ANY pending deadline
;; (`os/io n` = at least n steps), so the LIST ORDER of T never affects the
;; reduction — only the times do. Stable-sorting T by time is therefore sound
;; and merges states that differ only in the order independent timers were
;; inserted.
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

;; ---------------------------------------------------------------------------
;; Observable output
;;
;; `wrap-for-model` binds the only `print` as
;;   (lambda (s) (set! ACC (string-append ACC s)))
;; so we locate the accumulator cell ACC by that closure's shape and read its
;; value — the output produced SO FAR, which is a prefix of the final output
;; because printing only ever appends. `accumulator-value` returns #f when there
;; is no such cell (a program with no `print`, or before the binding exists);
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

;; The OBSERVED output of a TERMINAL state: what the real process's stdout
;; shows at exit — everything printed by the time every thread finished.
;; The root's return value is instead a SNAPSHOT of the accumulator taken at
;; the root's own last step: a worker's tail print (real behavior — a
;; mid-poll worker finishing after block_on returns; observed 2/20 runs on
;; tokio) lands after that read and is invisible through the root value.
;; Falls back to the root value for programs with no print accumulator
;; (value-returning programs).
(define (observed-output state)
  (define acc (accumulator-value state))
  (if (string? acc) acc (program-output state)))
