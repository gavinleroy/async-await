#lang racket/base

(require racket/cmdline
         racket/format
         racket/string
         racket/match
         (only-in racket/list make-list)
         "generate.rkt"
         "run.rkt"
         "../platform.rkt"
         "../typecheck.rkt"
         "../aio.rkt"
         "../tokio.rkt"
         "../trio.rkt"
         "../smol.rkt"
         "../javascript.rkt"
         "../swift.rkt"
         "../csharp.rkt")

;; ---------------------------------------------------------------------------
;; Configuration
;; ---------------------------------------------------------------------------

(define count     (make-parameter 10))
(define term-size (make-parameter 3))
(define max-steps (make-parameter 500))
(define threads   (make-parameter 2))
(define verbose?  (make-parameter #f))
(define selected  (make-parameter #f))

(define all-language-names
  '(asyncio tokio trio smol javascript swift csharp))

(define reducers
  (hasheq 'asyncio    -->aio
          'tokio      -->tokio
          'trio       -->trio
          'smol       -->smol
          'javascript -->js
          'swift      -->swift
          'csharp     -->c#))

(define runners
  (hasheq 'asyncio    compile-and-run-asyncio
          'tokio      compile-and-run-tokio
          'trio       compile-and-run-trio
          'smol       compile-and-run-smol
          'javascript compile-and-run-js
          'swift      compile-and-run-swift
          'csharp     compile-and-run-cs))

;; ---------------------------------------------------------------------------
;; Model execution
;; ---------------------------------------------------------------------------

(define (wrap-expr e nthreads)
  `(0 () () () ((thread (root ,e)) ,@(make-list nthreads '(thread)))))

(define (run-model red e)
  (with-handlers ([exn:fail? (lambda (exn) (values 'error (exn-message exn)))])
    (define prog (wrap-expr e (threads)))
    (define result (reduce red prog
                           #:max-steps (max-steps)
                           #:deterministic? #f))
    (if result
        (values 'ok (program-output result))
        (values 'stuck #f))))

;; ---------------------------------------------------------------------------
;; Runtime execution
;; ---------------------------------------------------------------------------

(define (run-runtime compile-and-run e)
  (with-handlers ([exn:fail? (lambda (exn) (values 'error (exn-message exn)))])
    (define r (compile-and-run e))
    (match (run-result-exit-code r)
      ['timeout (values 'timeout #f)]
      [0        (values 'ok (string-trim (run-result-stdout r)))]
      [_        (values 'crash (string-trim (run-result-stderr r)))])))

;; ---------------------------------------------------------------------------
;; Value comparison
;; ---------------------------------------------------------------------------

(define (model-value->string v)
  (match v
    [(? exact-integer?) (number->string v)]
    [(? string?) v]
    [#t "#true"]
    [#f "#false"]
    ['(void) "void"]
    [_ (~s v)]))

(define (values-match? model-val runtime-str)
  (define model-str (model-value->string model-val))
  (or (equal? model-str runtime-str)
      (and (string? model-val) (equal? model-val runtime-str))
      ;; bool representations differ across languages
      (and (boolean? model-val)
           (member runtime-str
                   (if model-val
                       '("True" "true" "True()" "1")
                       '("False" "false" "False()" "0"))))
      ;; void/unit representations
      (and (equal? model-val '(void))
           (member runtime-str '("None" "undefined" "null" "()" "")))))

;; ---------------------------------------------------------------------------
;; Per-language fuzzer
;; ---------------------------------------------------------------------------

(struct stats (pass mismatch model-stuck model-error
                    runtime-crash runtime-timeout gen-fail)
  #:transparent #:mutable)

(define (make-stats) (stats 0 0 0 0 0 0 0))
(define (stats-total s)
  (+ (stats-pass s) (stats-mismatch s) (stats-model-stuck s)
     (stats-model-error s) (stats-runtime-crash s)
     (stats-runtime-timeout s) (stats-gen-fail s)))

(define (bump! s field)
  (match field
    ['pass            (set-stats-pass! s (add1 (stats-pass s)))]
    ['mismatch        (set-stats-mismatch! s (add1 (stats-mismatch s)))]
    ['model-stuck     (set-stats-model-stuck! s (add1 (stats-model-stuck s)))]
    ['model-error     (set-stats-model-error! s (add1 (stats-model-error s)))]
    ['runtime-crash   (set-stats-runtime-crash! s (add1 (stats-runtime-crash s)))]
    ['runtime-timeout (set-stats-runtime-timeout! s (add1 (stats-runtime-timeout s)))]
    ['gen-fail        (set-stats-gen-fail! s (add1 (stats-gen-fail s)))]))

(define (fuzz-language lang)
  (printf "--- ~a ---~n" lang)
  (define red (hash-ref reducers lang))
  (define compile-and-run (hash-ref runners lang))
  (define st (make-stats))

  (for ([i (in-range (count))])
    (define raw-e
      (with-handlers ([exn:fail? (lambda (exn)
                                   (when (verbose?)
                                     (eprintf "  [~a] generation failed: ~a~n" i (exn-message exn)))
                                   #f)])
        (generate-expr lang #:size (term-size))))

    (cond
      [(not raw-e)
       (bump! st 'gen-fail)]
      [else
       (define-values (typed-e _type) (type-check raw-e))
       (cond
         [(not typed-e)
          (bump! st 'gen-fail)
          (when (verbose?) (eprintf "  [~a] type-check failed~n" i))]
         [else
          (define-values (m-status m-val) (run-model red raw-e))
          (define-values (r-status r-val) (run-runtime compile-and-run typed-e))

          (when (verbose?)
            (printf "  [~a] model=~a runtime=~a~n" i m-status r-status)
            (printf "       model-val=~s runtime-val=~s~n" m-val r-val))

          (match* (m-status r-status)
            [('ok 'ok)
             (if (values-match? m-val r-val)
                 (bump! st 'pass)
                 (begin
                   (bump! st 'mismatch)
                   (printf "  [~a] MISMATCH model=~s runtime=~s~n" i m-val r-val)
                   (when (verbose?)
                     (printf "       expr: ~s~n" raw-e))))]
            [('stuck _)     (bump! st 'model-stuck)]
            [('error _)     (bump! st 'model-error)]
            [(_ 'crash)
             (bump! st 'runtime-crash)
             (printf "  [~a] CRASH ~a~n" i (if (verbose?) r-val ""))]
            [(_ 'timeout)   (bump! st 'runtime-timeout)]
            [(_ _)          (bump! st 'mismatch)])])]))

  (printf "  pass: ~a  mismatch: ~a  model-stuck: ~a  model-error: ~a~n"
          (stats-pass st) (stats-mismatch st) (stats-model-stuck st) (stats-model-error st))
  (printf "  runtime-crash: ~a  runtime-timeout: ~a  gen-fail: ~a  (of ~a)~n"
          (stats-runtime-crash st) (stats-runtime-timeout st) (stats-gen-fail st) (count))
  st)

;; ---------------------------------------------------------------------------
;; Entry point
;; ---------------------------------------------------------------------------

(module+ main
  (command-line
   #:program "async-fuzz"
   #:once-each
   [("-n" "--count") n
    "Programs per language (default: 10)"
    (count (string->number n))]
   [("-s" "--size") s
    "Term generation size (default: 3)"
    (term-size (string->number s))]
   [("--max-steps") m
    "Max model reduction steps (default: 500)"
    (max-steps (string->number m))]
   [("--threads") t
    "Worker threads in model (default: 2)"
    (threads (string->number t))]
   [("-v" "--verbose")
    "Show per-program details"
    (verbose? #t)]
   #:multi
   [("-l" "--lang") l
    "Language to test (repeatable; default: all)"
    (selected (cons (string->symbol l) (or (selected) '())))])

  (define langs
    (cond
      [(selected) => (lambda (sel)
                       (for ([l (in-list sel)])
                         (unless (memq l all-language-names)
                           (eprintf "unknown language: ~a~n" l)
                           (exit 1)))
                       sel)]
      [else all-language-names]))

  (printf "async-fuzz: ~a programs × ~a languages (size=~a, max-steps=~a)~n"
          (count) (length langs) (term-size) (max-steps))

  (define results
    (for/list ([lang (in-list langs)])
      (cons lang (fuzz-language lang))))

  (newline)
  (printf "=== summary ===~n")
  (define total-pass 0)
  (define total-fail 0)
  (for ([r (in-list results)])
    (define st (cdr r))
    (define fails (+ (stats-mismatch st) (stats-runtime-crash st)))
    (set! total-pass (+ total-pass (stats-pass st)))
    (set! total-fail (+ total-fail fails))
    (when (> fails 0)
      (printf "  ~a: ~a failures~n" (car r) fails)))
  (printf "total: ~a pass, ~a fail~n" total-pass total-fail)
  (exit (if (zero? total-fail) 0 1)))
