#lang racket/base

;; -----------------------------------------------------------------------------
;; Differential fuzzer.
;;
;; For each generated, well-typed program:
;;   - the MODEL is sampled K times (nondeterministic reduction); its outputs
;;     form the specification set,
;;   - the REAL program is compiled once and run R times,
;;   - the claim under test: every real-world output is a member of the
;;     model's output set.
;; On a membership miss the model is resampled (up to 10xK extra runs)
;; before the miss is reported — sampling can under-approximate the set.
;;
;; Generated programs evaluate to "<trace>|<value>" strings (see typegen.rkt),
;; so model values and runtime stdout compare as plain strings.
;; -----------------------------------------------------------------------------

(require racket/cmdline
         racket/match
         racket/string
         (only-in racket/list make-list remove-duplicates)
         "typegen.rkt"
         "run.rkt"
         "../platform.rkt"
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

(define count         (make-parameter 10))
(define model-samples (make-parameter 2))
(define runtime-runs  (make-parameter 50))
(define max-steps     (make-parameter 5000))
(define threads       (make-parameter #f)) ; #f = per-language default
(define verbose?      (make-parameter #f))
(define selected      (make-parameter #f))

;; Worker threads in the model must match the runtime's concurrency model:
;; asyncio/trio/JS event loops are single-threaded — giving the model extra
;; threads produces interleavings (e.g. a spawned task running before its
;; creator suspends) that the real runtime cannot exhibit, and vice versa
;; hides orderings the runtime guarantees.
(define model-threads
  (hasheq 'asyncio    1
          'trio       1
          'javascript 1
          'tokio      2
          'smol       2
          'swift      2
          'csharp     2))

(define (threads-for lang)
  (or (threads) (hash-ref model-threads lang 2)))

(define reducers
  (hasheq 'asyncio    -->aio
          'tokio      -->tokio
          'trio       -->trio
          'smol       -->smol
          'javascript -->js
          'swift      -->swift
          'csharp     -->c#))

;; ---------------------------------------------------------------------------
;; Model: sample the reduction relation
;; ---------------------------------------------------------------------------

;; Generated programs use `(print e)` forms. The compilers treat print as a
;; built-in writing to real stdout; for the model the same s-expression is
;; an application of the `print` lambda bound here — the trace-stdout
;; expansion from core.rkt's niceties, spelled out in grammar forms. The
;; wrapped program evaluates to the accumulated trace (the program itself
;; evaluates to "", so the begin's value is exactly what was printed).
;; Prints are not racy in the model: only one thread evaluates at a time.
(define (wrap-for-model e)
  `(let ([stdout ""])
     (let ([print (lambda (s) (set! stdout (string-append stdout s)))])
       (begin ,e stdout))))

(define (wrap-expr e nthreads)
  `(0 () () () ((thread (root ,(wrap-for-model e)))
                ,@(make-list nthreads '(thread)))))

;; One nondeterministic model run: 'ok + value | 'stuck | 'error
(define (run-model-once red e nthreads)
  (with-handlers ([exn:fail? (lambda (exn) (values 'error (exn-message exn)))])
    (define result (reduce red (wrap-expr e nthreads)
                           #:max-steps (max-steps)
                           #:deterministic? #f))
    (define out (and result (program-output result)))
    (if (string? out)
        (values 'ok out)
        (values 'stuck #f))))

;; Sample k model runs; returns (values outputs stuck-count error-count first-error)
(define (sample-model red e k nthreads)
  (for/fold ([outs '()] [stuck 0] [errs 0] [msg #f]
             #:result (values (remove-duplicates outs) stuck errs msg))
            ([_ (in-range k)])
    (define-values (status val) (run-model-once red e nthreads))
    (match status
      ['ok    (values (cons val outs) stuck errs msg)]
      ['stuck (values outs (add1 stuck) errs msg)]
      ['error (values outs stuck (add1 errs) (or msg val))])))

;; ---------------------------------------------------------------------------
;; Per-language fuzzer
;; ---------------------------------------------------------------------------

(struct stats (pass mismatch model-stuck model-error
                    runtime-crash runtime-timeout gen-fail)
  #:transparent #:mutable)

(define (make-stats) (stats 0 0 0 0 0 0 0))

(define (bump! s field)
  (match field
    ['pass            (set-stats-pass! s (add1 (stats-pass s)))]
    ['mismatch        (set-stats-mismatch! s (add1 (stats-mismatch s)))]
    ['model-stuck     (set-stats-model-stuck! s (add1 (stats-model-stuck s)))]
    ['model-error     (set-stats-model-error! s (add1 (stats-model-error s)))]
    ['runtime-crash   (set-stats-runtime-crash! s (add1 (stats-runtime-crash s)))]
    ['runtime-timeout (set-stats-runtime-timeout! s (add1 (stats-runtime-timeout s)))]
    ['gen-fail        (set-stats-gen-fail! s (add1 (stats-gen-fail s)))]))

(define (fuzz-one lang red st i)
  (define p
    (with-handlers ([exn:fail? (lambda (exn)
                                 (when (verbose?)
                                   (eprintf "  [~a] generation failed: ~a~n"
                                            i (exn-message exn)))
                                 #f)])
      (generate-program lang)))
  (cond
    [(not p) (bump! st 'gen-fail)]
    [else
     (define term (gen-program-term p))

     ;; 1. the model's output set
     (define-values (model-outs stuck errs err-msg)
       (sample-model red term (model-samples) (threads-for lang)))
     (cond
       [(null? model-outs)
        (bump! st (if (> errs 0) 'model-error 'model-stuck))
        (when (verbose?)
          (printf "  [~a] model ~a~a~n" i (if (> errs 0) "error" "stuck")
                  (if err-msg (format ": ~a" err-msg) ""))
          (printf "       expr: ~s~n" term))]
       [else
        ;; 2. sample the real program
        (define results (compile-and-run-many lang (gen-program-annotated p)
                                              (runtime-runs)))
        (define crash (findf (lambda (r)
                               (and (not (eq? (run-result-exit-code r) 'timeout))
                                    (not (zero? (run-result-exit-code r)))))
                             results))
        (define timeout (findf (lambda (r) (eq? (run-result-exit-code r) 'timeout))
                               results))
        (cond
          [crash
           (bump! st 'runtime-crash)
           (printf "  [~a] CRASH ~a~n" i (string-trim (run-result-stderr crash)))
           (when (verbose?) (printf "       expr: ~s~n" term))]
          [timeout (bump! st 'runtime-timeout)]
          [else
           (define runtime-outs
             (remove-duplicates (map (lambda (r) (string-trim (run-result-stdout r)))
                                     results)))
           ;; 3. membership, with escalation: sampling can under-approximate
           ;;    the model's set, so resample before reporting a miss
           (define misses
             (for/list ([out (in-list runtime-outs)]
                        #:unless (member out model-outs))
               out))
           (define-values (extra-outs _s _e _m)
             (if (null? misses)
                 (values '() 0 0 #f)
                 (sample-model red term (* 10 (model-samples)) (threads-for lang))))
           (define model-set (remove-duplicates (append model-outs extra-outs)))
           (define real-misses
             (for/list ([out (in-list misses)]
                        #:unless (member out model-set))
               out))
           (cond
             [(null? real-misses)
              (bump! st 'pass)
              (when (verbose?)
                (printf "  [~a] pass: ~a runtime outputs ⊆ ~a model outputs~n"
                        i (length runtime-outs) (length model-set)))]
             [else
              (bump! st 'mismatch)
              (printf "  [~a] MISMATCH: runtime output(s) ~s not in model set ~s~n"
                      i real-misses model-set)
              (printf "       expr: ~s~n" term)])])])]))

(define (fuzz-language lang)
  (printf "--- ~a ---~n" lang)
  (define red (hash-ref reducers lang))
  (define st (make-stats))
  (for ([i (in-range (count))])
    (fuzz-one lang red st i))
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
   [("-k" "--model-samples") k
    "Model runs per program (default: 2; escalates 10x on a membership miss)"
    (model-samples (string->number k))]
   [("-r" "--runtime-runs") r
    "Real-program runs per program (default: 50)"
    (runtime-runs (string->number r))]
   [("--max-steps") m
    "Max model reduction steps (default: 5000)"
    (max-steps (string->number m))]
   [("--threads") t
    "Override worker threads in model (default: per-language)"
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
                         (unless (memq l typegen-languages)
                           (eprintf "unknown language: ~a~n" l)
                           (exit 1)))
                       sel)]
      [else typegen-languages]))

  (printf "async-fuzz: ~a programs × ~a languages (model-samples=~a, runtime-runs=~a)~n"
          (count) (length langs) (model-samples) (runtime-runs))

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
