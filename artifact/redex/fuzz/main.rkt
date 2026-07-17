#lang racket/base

;; -----------------------------------------------------------------------------
;; Differential fuzzer.
;;
;; RUNTIME-FIRST, for each generated, well-typed program:
;;   - the REAL program is compiled once and run R times; its distinct outputs
;;     are the membership targets,
;;   - ONE multi-target witness search on the non-collapsing relation
;;     (fuzz/witness.rkt) decides for every target at once whether the model
;;     can produce it; the search's walk phase doubles as directed model
;;     sampling. A proven-unreachable output is a confirmed mismatch; one we
;;     cannot decide within budget is reported as `unconfirmed`.
;;   - the claim under test: every real-world output is a member of the
;;     model's output set.
;;
;; Generated programs evaluate to "<trace>|<value>" strings (see typegen.rkt),
;; so model values and runtime stdout compare as plain strings.
;; -----------------------------------------------------------------------------

(require racket/cmdline
         racket/file
         racket/match
         racket/string
         racket/place
         racket/runtime-path
         json
         (only-in racket/list remove-duplicates)
         (only-in "model.rkt" wrap-program)
         (only-in "witness.rkt" multi-witness-search)
         ;; not used directly here — required so `raco make fuzz/main.rkt`
         ;; compiles the place-worker module dynamic-place loads at runtime
         (only-in "witness-place.rkt" witness-place-main)
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
(define runtime-runs  (make-parameter 50))
(define threads       (make-parameter #f)) ; #f = per-language default
(define verbose?      (make-parameter #f))
(define selected      (make-parameter #f))
(define seed          (make-parameter #f)) ; #f until chosen; always set before fuzzing
(define out-dir       (make-parameter #f)) ; run cache directory (JSONL + summaries)

;; Per-language RNG seed. Each language re-seeds from this base before generating
;; its programs, so `-l <lang> --seed N` reproduces exactly the same programs for
;; that language regardless of which other languages share the run. The base name
;; is folded in so distinct languages don't generate identical program streams.
(define (language-seed base lang)
  (define name-sum
    (for/sum ([c (in-string (symbol->string lang))]) (char->integer c)))
  (add1 (modulo (+ (* base 1000003) name-sum) 1000000006)))

;; Every runtime output is resolved by the directed witness search on the
;; non-collapsing relation (-->>lang). These bound that search: finding a
;; witness is cheap, but PROVING an output unreachable can cost as much as
;; full enumeration. The budget is only SPENT when targets resist the walk
;; phase (a typical pass finishes in seconds), so the default is generous:
;; a Redex step costs 40-80ms on these models, and deep interleavings need
;; thousands of steps to witness.
;;
;; `search-workers` place workers per lane run extra walk batteries in
;; parallel with independent RNG (fuzz/witness-place.rkt); 0 disables the
;; pool. Each worker is a full OS thread running its own Redex instance.
(define witness-states (make-parameter 300000))
(define witness-ms     (make-parameter 300000))
(define search-workers (make-parameter 2))

;; Lazily-created, lane-lifetime pool of walk workers (each loads every model,
;; a few seconds once per lane).
(define-runtime-path witness-place-path "witness-place.rkt")
(define worker-pool '())
(define (ensure-pool!)
  (when (and (null? worker-pool) (> (search-workers) 0))
    (set! worker-pool
          (for/list ([i (in-range (search-workers))])
            (define pl (dynamic-place witness-place-path 'witness-place-main))
            (place-channel-put pl i)
            pl)))
  worker-pool)

;; Worker threads in the model must match the runtime's concurrency model:
;; event loops are single-threaded — giving the model extra threads produces
;; interleavings (e.g. a spawned task running before its creator suspends)
;; that the real runtime cannot exhibit, and vice versa hides orderings the
;; runtime guarantees. asyncio/trio/JS need NO worker slot: their scheduler
;; rules run ready thunks as frames stacked on the root thread (the event
;; loop IS the one thread).
;; smol is 1: block_on drives the entry future inline on the root thread
;; (see smol.rkt os/block-coro) in parallel with ONE executor thread --
;; smol's global executor defaults to a single worker (SMOL_THREADS unset).
;; tokio is 4: #[tokio::main] defaults to worker_threads = cores (probed:
;; >=3 distinct worker ids), and generated programs spawn at most ~4 tasks;
;; fewer model slots than concurrently-runnable tasks hides real parallel
;; interleavings.
;; swift is 4 for the same reason as tokio: the global concurrent executor is
;; core-width (>=4 anywhere), and with only 2 slots + FIFO dispatch a third
;; task PROVABLY cannot print before two stalled predecessors (fuzz seed
;; 227726474 swift[12]/[13]: "DCAAABBB|0"/"AADCABBB|0" enumeration-exhausted
;; unreachable, yet the real runtime produced them).
(define model-threads
  (hasheq 'asyncio    0
          'trio       0
          'javascript 0
          'tokio      4
          'smol       1
          'swift      4
          'csharp     2))

(define (threads-for lang)
  (or (threads) (hash-ref model-threads lang 2)))

;; Non-collapsing variants (-->>lang), for the directed witness search.
(define witness-reducers
  (hasheq 'asyncio    -->>aio
          'tokio      -->>tokio
          'trio       -->>trio
          'smol       -->>smol
          'javascript -->>js
          'swift      -->>swift
          'csharp     -->>c#))

;; ---------------------------------------------------------------------------
;; Per-language fuzzer
;; ---------------------------------------------------------------------------

;; `mismatch`    : a real output the model PROVABLY cannot produce (confirmed bug).
;; `unconfirmed` : a real output we could not witness in the model within budget
;;                 (neither found nor proven absent) — needs a bigger budget or a
;;                 human look, but not a confirmed failure.
(struct stats (pass mismatch unconfirmed
                    runtime-crash runtime-timeout gen-fail)
  #:transparent #:mutable)

(define (make-stats) (stats 0 0 0 0 0 0))

(define (bump! s field)
  (match field
    ['pass            (set-stats-pass! s (add1 (stats-pass s)))]
    ['mismatch        (set-stats-mismatch! s (add1 (stats-mismatch s)))]
    ['unconfirmed     (set-stats-unconfirmed! s (add1 (stats-unconfirmed s)))]
    ['runtime-crash   (set-stats-runtime-crash! s (add1 (stats-runtime-crash s)))]
    ['runtime-timeout (set-stats-runtime-timeout! s (add1 (stats-runtime-timeout s)))]
    ['gen-fail        (set-stats-gen-fail! s (add1 (stats-gen-fail s)))]))

;; One JSONL record per program, appended EAGERLY so a running lane can be
;; inspected mid-flight (and later rendered by a TUI).
(define (write-record! lang rec)
  (when (out-dir)
    (call-with-output-file (build-path (out-dir) (format "~a.jsonl" lang))
      #:exists 'append
      (lambda (p) (write-json rec p) (newline p)))))

(define (now-ms) (current-inexact-milliseconds))

(define (fuzz-one lang st i)
  (define t0 (now-ms))
  (define p
    (with-handlers ([exn:fail? (lambda (exn)
                                 (when (verbose?)
                                   (eprintf "  [~a] generation failed: ~a~n"
                                            i (exn-message exn)))
                                 #f)])
      (generate-program lang)))
  (cond
    [(not p)
     (bump! st 'gen-fail)
     (write-record! lang (hasheq 'index i 'status "gen-fail"))]
    [else
     (define term (gen-program-term p))
     (define (record! status counts verdicts ms-extra)
       (write-record!
        lang
        (hasheq 'index i
                'status status
                'term (format "~s" term)
                'outputs (for/list ([o (in-list (hash-keys counts))])
                           (hasheq 'out o
                                   'count (hash-ref counts o)
                                   'verdict (hash-ref verdicts o "unknown")))
                'ms (hash-set ms-extra 'total (round (- (now-ms) t0))))))

     ;; 1. the real program: build once, run R times, count distinct outputs
     (let ()
        (define t-run0 (now-ms))
        (define results (compile-and-run-many lang (gen-program-annotated p)
                                              (runtime-runs)))
        (define t-run (round (- (now-ms) t-run0)))
        (define crash (findf (lambda (r)
                               (and (not (eq? (run-result-exit-code r) 'timeout))
                                    (not (zero? (run-result-exit-code r)))))
                             results))
        (define timeout (findf (lambda (r) (eq? (run-result-exit-code r) 'timeout))
                               results))
        (cond
          [crash
           (bump! st 'runtime-crash)
           (record! "runtime-crash" (hash) (hash) (hasheq 'runtime t-run))
           (printf "  [~a] CRASH ~a~n" i (string-trim (run-result-stderr crash)))
           (printf "       expr: ~s~n" term)
           (flush-output)]
          [timeout
           (bump! st 'runtime-timeout)
           (record! "runtime-timeout" (hash) (hash) (hasheq 'runtime t-run))
           (printf "  [~a] runtime TIMEOUT~n" i)
           (printf "       expr: ~s~n" term)
           (flush-output)]
          [else
           (define counts
             (for/fold ([h (hash)]) ([r (in-list results)])
               (hash-update h (string-trim (run-result-stdout r)) add1 0)))
           (define runtime-outs (hash-keys counts))

           ;; 2. membership: ONE multi-target search for every distinct
           ;;    runtime output. The walk phase resolves the common outputs in
           ;;    milliseconds (it IS the model sampler, directed at exactly
           ;;    the outputs reality produced); a single union-pruned DFS
           ;;    proves any leftovers unreachable together (witness.rkt).
           (define misses runtime-outs)
           (define t-search0 (now-ms))
           (define search-verdicts
             (multi-witness-search (hash-ref witness-reducers lang)
                                   (wrap-program term (threads-for lang))
                                   misses
                                   #:state-cap (witness-states)
                                   #:time-cap  (witness-ms)
                                   #:pool      (ensure-pool!)
                                   #:lang      lang))
           (define t-search (round (- (now-ms) t-search0)))
           (define verdicts
             (for/hash ([o (in-list runtime-outs)])
               (values o (symbol->string
                          (hash-ref search-verdicts o 'inconclusive)))))
           (define confirmed
             (for/list ([o (in-list misses)]
                        #:when (eq? (hash-ref search-verdicts o #f) 'unreachable))
               o))
           (define unconfirmed
             (for/list ([o (in-list misses)]
                        #:when (eq? (hash-ref search-verdicts o #f) 'inconclusive))
               o))
           (define ms (hasheq 'runtime t-run 'search t-search))
           (cond
             [(pair? confirmed)
              (bump! st 'mismatch)
              (record! "mismatch" counts verdicts ms)
              (printf "  [~a] MISMATCH: model cannot produce runtime output(s) ~s~n" i confirmed)
              (when (pair? unconfirmed)
                (printf "       (also unconfirmed within budget: ~s)~n" unconfirmed))
              (printf "       expr: ~s~n" term)]
             [(pair? unconfirmed)
              (bump! st 'unconfirmed)
              (record! "unconfirmed" counts verdicts ms)
              (printf "  [~a] UNCONFIRMED: could not witness runtime output(s) ~s in the model within budget (~ams)~n"
                      i unconfirmed (witness-ms))
              (printf "       expr: ~s~n" term)]
             [else
              (bump! st 'pass)
              (record! "pass" counts verdicts ms)
              (printf "  [~a] pass: ~a output~a in ~as~n"
                      i (length runtime-outs)
                      (if (= 1 (length runtime-outs)) "" "s")
                      (/ (round (/ (- (now-ms) t0) 100)) 10.0))])
           (flush-output)]))]))


(define (fuzz-language lang)
  (printf "--- ~a ---~n" lang)
  (flush-output)
  (random-seed (language-seed (seed) lang))
  (define st (make-stats))
  (define t0 (now-ms))
  (for ([i (in-range (count))])
    (fuzz-one lang st i))
  (when (out-dir)
    (call-with-output-file (build-path (out-dir) (format "~a-summary.json" lang))
      #:exists 'replace
      (lambda (p)
        (write-json
         (hasheq 'lang (symbol->string lang)
                 'seed (seed)
                 'count (count)
                 'pass (stats-pass st)
                 'mismatch (stats-mismatch st)
                 'unconfirmed (stats-unconfirmed st)
                 'runtime-crash (stats-runtime-crash st)
                 'runtime-timeout (stats-runtime-timeout st)
                 'gen-fail (stats-gen-fail st)
                 'wall-ms (round (- (now-ms) t0)))
         p))))
  (printf "  pass: ~a  mismatch: ~a  unconfirmed: ~a~n"
          (stats-pass st) (stats-mismatch st) (stats-unconfirmed st))
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
   [("--out") dir
    "Run cache directory: per-lane JSONL records and summaries are written here"
    (out-dir dir)]
   [("--seed") s
    "RNG seed for reproducible program generation (default: a fresh one, printed)"
    (seed (string->number s))]
   [("-r" "--runtime-runs") r
    "Real-program runs per program (default: 50)"
    (runtime-runs (string->number r))]
   [("--witness-time") wt
    "Per-program multi-target search time budget in ms (default: 300000)"
    (witness-ms (string->number wt))]
   [("--witness-states") ws
    "Per-program multi-target search state budget (default: 300000)"
    (witness-states (string->number ws))]
   [("--search-workers") sw
    "Parallel walk workers per lane, 0 disables the pool (default: 2)"
    (search-workers (string->number sw))]
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

  ;; Always run with a definite seed, and print it, so every run is reproducible:
  ;; re-run with `--seed <printed>` to regenerate the exact same programs.
  (unless (seed) (seed (random 1000000007)))

  (when (out-dir)
    (make-directory* (out-dir)))

  (printf "async-fuzz: ~a programs × ~a languages (seed=~a, runtime-runs=~a)~n"
          (count) (length langs) (seed) (runtime-runs))
  (flush-output)

  (define results
    (for/list ([lang (in-list langs)])
      (cons lang (fuzz-language lang))))

  (newline)
  (printf "=== summary ===~n")
  (define total-pass 0)
  (define total-fail 0)
  (define total-unconfirmed 0)
  (for ([r (in-list results)])
    (define st (cdr r))
    (define fails (+ (stats-mismatch st) (stats-runtime-crash st)))
    (set! total-pass (+ total-pass (stats-pass st)))
    (set! total-fail (+ total-fail fails))
    (set! total-unconfirmed (+ total-unconfirmed (stats-unconfirmed st)))
    (when (or (> fails 0) (> (stats-unconfirmed st) 0))
      (printf "  ~a: ~a failures~a~n" (car r) fails
              (if (> (stats-unconfirmed st) 0)
                  (format ", ~a unconfirmed" (stats-unconfirmed st))
                  ""))))
  (printf "total: ~a pass, ~a fail~a~n" total-pass total-fail
          (if (> total-unconfirmed 0) (format ", ~a unconfirmed" total-unconfirmed) ""))
  ;; unconfirmed outputs are not counted as hard failures (we could not prove a
  ;; divergence), but they are surfaced above for investigation.
  (exit (if (zero? total-fail) 0 1)))
