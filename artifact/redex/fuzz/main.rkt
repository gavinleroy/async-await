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
;; `search-workers` place workers per lane each run a whole program's
;; multi-target search as one job (fuzz/witness-place.rkt), so several
;; programs' searches proceed concurrently; 0 disables the pool (searches
;; then run locally in sequence). Each worker is a full OS thread running
;; its own Redex instance.
(define witness-states (make-parameter 300000))
(define witness-ms     (make-parameter 300000))
(define search-workers (make-parameter 3))

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

;; The real-program stage of program i+1 (compile once + R runs, all
;; subprocess-bound) runs on a green thread WHILE program i's witness search
;; (racket-CPU-bound) runs — the two stages of adjacent programs overlap,
;; one runtime job in flight at a time.
(define (start-runtime lang p)
  (and p
       (let ([ch (make-channel)])
         (thread
          (lambda ()
            (define t0 (now-ms))
            (define r (with-handlers ([(lambda (_) #t) (lambda (e) (cons 'exn e))])
                        (cons 'ok (compile-and-run-many lang (gen-program-annotated p)
                                                        (runtime-runs)))))
            (channel-put ch (list r (round (- (now-ms) t0))))))
         ch)))

(define (finish-runtime ch)
  (match (channel-get ch)
    [(list (cons 'ok results) ms) (values results ms)]
    [(list (cons 'exn e) _) (raise e)]))

;; Program generation draws from ITS OWN PRNG stream (see fuzz-language):
;; the witness search's walks also call `random`, and their draw count is
;; budget/timing-dependent — on a shared stream program i+1 depends on how
;; long search i ran, and `--seed` pins nothing past the first program
;; (observed: two same-seed runs agreed only on index 0). Searches are
;; instead seeded deterministically per (seed, lang, index).
(define (search-seed lang i)
  (modulo (+ (language-seed (seed) lang) (* 7919 (add1 i)))
          (sub1 (expt 2 31))))

;; Everything a program's search stage needs, computed from its runtime batch.
(struct search-ctx (i term start counts runtime-outs t-run) #:transparent)

;; Stage 1: consume the runtime batch. Writes the terminal record for
;; gen-fail / runtime-crash / runtime-timeout and returns #f; otherwise
;; returns a `search-ctx` for the search stage.
(define (prepare-program lang st i p results t-run)
  (cond
    [(not p)
     (bump! st 'gen-fail)
     (write-record! lang (hasheq 'index i 'status "gen-fail"))
     #f]
    [else
     (define term (gen-program-term p))
     (define (record-simple! status)
       (write-record!
        lang
        (hasheq 'index i 'status status 'term (format "~s" term)
                'outputs '()
                'ms (hasheq 'runtime t-run 'total t-run))))
     (define crash (findf (lambda (r)
                            (and (not (eq? (run-result-exit-code r) 'timeout))
                                 (not (zero? (run-result-exit-code r)))))
                          results))
     (define timeout (findf (lambda (r) (eq? (run-result-exit-code r) 'timeout))
                            results))
     (cond
       [crash
        (bump! st 'runtime-crash)
        (record-simple! "runtime-crash")
        (printf "  [~a] CRASH ~a~n" i (string-trim (run-result-stderr crash)))
        (printf "       expr: ~s~n" term)
        (flush-output)
        #f]
       [timeout
        (bump! st 'runtime-timeout)
        (record-simple! "runtime-timeout")
        (printf "  [~a] runtime TIMEOUT~n" i)
        (printf "       expr: ~s~n" term)
        (flush-output)
        #f]
       [else
        (define counts
          (for/fold ([h (hash)]) ([r (in-list results)])
            (hash-update h (string-trim (run-result-stdout r)) add1 0)))
        (search-ctx i term (wrap-program term (threads-for lang))
                    counts (hash-keys counts) t-run)])]))

;; Stage 2: fold the search's verdicts into the record, stats, and log line.
(define (finish-program lang st ctx search-verdicts t-search)
  (match-define (search-ctx i term _start counts runtime-outs t-run) ctx)
  (define verdicts
    (for/hash ([o (in-list runtime-outs)])
      (values o (symbol->string (hash-ref search-verdicts o 'inconclusive)))))
  (define confirmed
    (for/list ([o (in-list runtime-outs)]
               #:when (eq? (hash-ref search-verdicts o #f) 'unreachable))
      o))
  (define unconfirmed
    (for/list ([o (in-list runtime-outs)]
               #:when (eq? (hash-ref search-verdicts o #f) 'inconclusive))
      o))
  (define (record! status)
    (write-record!
     lang
     (hasheq 'index i 'status status 'term (format "~s" term)
             'outputs (for/list ([o (in-list (hash-keys counts))])
                        (hasheq 'out o
                                'count (hash-ref counts o)
                                'verdict (hash-ref verdicts o "unknown")))
             'ms (hasheq 'runtime t-run 'search t-search
                         'total (+ t-run t-search)))))
  (cond
    [(pair? confirmed)
     (bump! st 'mismatch)
     (record! "mismatch")
     (printf "  [~a] MISMATCH: model cannot produce runtime output(s) ~s~n" i confirmed)
     (when (pair? unconfirmed)
       (printf "       (also unconfirmed within budget: ~s)~n" unconfirmed))
     (printf "       expr: ~s~n" term)]
    [(pair? unconfirmed)
     (bump! st 'unconfirmed)
     (record! "unconfirmed")
     (printf "  [~a] UNCONFIRMED: could not witness runtime output(s) ~s in the model within budget (~ams)~n"
             i unconfirmed (witness-ms))
     (printf "       expr: ~s~n" term)]
    [else
     (bump! st 'pass)
     (record! "pass")
     (printf "  [~a] pass: ~a output~a in ~as~n"
             i (length runtime-outs)
             (if (= 1 (length runtime-outs)) "" "s")
             (/ (round (/ (+ t-run t-search) 100)) 10.0))])
  (flush-output))


(define (fuzz-language lang)
  (printf "--- ~a ---~n" lang)
  (flush-output)
  (define st (make-stats))
  (define t0 (now-ms))
  ;; generate the whole program stream first, each program from its own
  ;; deterministic typegen seed — program i is a pure function of
  ;; (--seed, lang, i), whatever any other stage's RNG does (typegen's
  ;; `current-rng` is its own parameter; parameterizing the ambient
  ;; generator around the call never reached it)
  (define progs
    (for/vector ([i (in-range (count))])
      (with-handlers ([exn:fail? (lambda (exn)
                                   (when (verbose?)
                                     (eprintf "  [~a] generation failed: ~a~n"
                                              i (exn-message exn)))
                                   #f)])
        (generate-program lang #:seed (search-seed lang i)))))
  (define n (count))
  ;; Search dispatch. With a place pool (`--search-workers`), each program's
  ;; ENTIRE multi-target search runs as one job on a free place, so several
  ;; programs' searches proceed concurrently — a slow lane's wall is a few
  ;; hard programs, and whole-search jobs are what let those overlap (a
  ;; hard search saturates its own process; extra walk helpers on the same
  ;; targets were worth less than a second program's search). Without a
  ;; pool, searches run locally in sequence.
  (define pool (ensure-pool!))
  (define free pool)
  (define in-flight '()) ; (list place ctx t-submitted)
  ;; TWO-PASS SEARCH (pool mode). Pass 1: each program's whole search runs
  ;; as one 1-process job at a REDUCED budget — breadth: several programs
  ;; concurrently, resolving the typical program in seconds. A program with
  ;; leftover targets is NOT finalized; at lane end (pass 2) it gets a LOCAL
  ;; search at the full budget with every (now idle) place running walk
  ;; batteries for it — depth: the strongest configuration, reserved for the
  ;; few programs that resist. This is escalation to a stronger setup, not a
  ;; same-setup retry: pass 1 is one process on a busy machine, pass 2 is
  ;; workers+1 processes on a drained one.
  ;; 90s: the typical program resolves in seconds; a genuine resister is
  ;; better served failing into the pooled pass 2 than grinding 1-process,
  ;; but every escalation costs serialized lane-end time, so pass 1 gets
  ;; enough rope to clear the merely-awkward programs itself.
  (define pass1-ms (min (witness-ms) 90000))
  (define escalations '()) ; (list ctx pass1-verdicts pass1-t) in arrival order
  (define (unresolved-of ctx verdicts)
    (for/list ([o (in-list (search-ctx-runtime-outs ctx))]
               #:when (eq? (hash-ref verdicts o 'inconclusive) 'inconclusive))
      o))
  (define (drain-one!)
    (match-define (cons (and e (list pl ctx t-sub)) msg)
      (apply sync
             (for/list ([e (in-list in-flight)])
               (wrap-evt (car e) (lambda (msg) (cons e msg))))))
    (set! in-flight (remq e in-flight))
    (set! free (cons pl free))
    (define v (for/hash ([kv (in-list msg)])
                (values (car kv) (cadr kv))))
    (define t (round (- (now-ms) t-sub)))
    (if (pair? (unresolved-of ctx v))
        (set! escalations (cons (list ctx v t) escalations))
        (finish-program lang st ctx v t)))
  (define (local-search ctx targets time-cap p00l)
    (random-seed (search-seed lang (search-ctx-i ctx)))
    (define t-s0 (now-ms))
    (define v (multi-witness-search (hash-ref witness-reducers lang)
                                    (search-ctx-start ctx)
                                    targets
                                    #:state-cap (witness-states)
                                    #:time-cap  time-cap
                                    #:pool      p00l
                                    #:lang      lang))
    (values v (round (- (now-ms) t-s0))))
  (define (dispatch-search! ctx)
    (cond
      [(null? pool)
       (define-values (v t)
         (local-search ctx (search-ctx-runtime-outs ctx) (witness-ms) '()))
       (finish-program lang st ctx v t)]
      [else
       (when (null? free) (drain-one!))
       (define pl (car free))
       (set! free (cdr free))
       (place-channel-put pl (vector 'search lang
                                     (search-ctx-start ctx)
                                     (search-ctx-runtime-outs ctx)
                                     pass1-ms (witness-states)
                                     (search-seed lang (search-ctx-i ctx))))
       (set! in-flight (cons (list pl ctx (now-ms)) in-flight))]))
  (let loop ([i 0]
             [cur (and (> n 0) (start-runtime lang (vector-ref progs 0)))])
    (when (< i n)
      (define p (vector-ref progs i))
      (define-values (results t-run)
        (if cur (finish-runtime cur) (values '() 0)))
      ;; kick off i+1's runtime before i's search so they overlap
      (define nxt (and (< (add1 i) n)
                       (start-runtime lang (vector-ref progs (add1 i)))))
      (define ctx (prepare-program lang st i p results t-run))
      (when ctx (dispatch-search! ctx))
      (loop (add1 i) nxt)))
  (let drain () (unless (null? in-flight) (drain-one!) (drain)))
  ;; Pass 2: resubmit each resister as a CONCURRENT full-budget job — the
  ;; conjunction biases resolve the known-hard families in well under the
  ;; budget at one process, and 3 concurrent escalations beat one 4-process
  ;; escalation at a time. Anything that STILL resists gets the final tier:
  ;; a local search with every idle place running walk batteries for it.
  (define pass2 '()) ; (list ctx merged-verdicts total-t)
  (set! in-flight '())
  (set! free pool)
  (for ([item (in-list (reverse escalations))])
    (match-define (list ctx v1 t1) item)
    (define unresolved (unresolved-of ctx v1))
    (printf "  [~a] pass 2: ~a target(s) resisted the ~as job; full-budget job~n"
            (search-ctx-i ctx) (length unresolved) (quotient pass1-ms 1000))
    (flush-output)
    (when (null? free)
      ;; inline drain for pass 2: collect one reply, record for tier 3
      (match-define (cons (and e (list pl ctx0 t-sub0 v0)) msg)
        (apply sync (for/list ([e (in-list in-flight)])
                      (wrap-evt (car e) (lambda (msg) (cons e msg))))))
      (set! in-flight (remq e in-flight))
      (set! free (cons pl free))
      (define v* (for/fold ([h v0]) ([kv (in-list msg)])
                   (hash-set h (car kv) (cadr kv))))
      (set! pass2 (cons (list ctx0 v* (round (- (now-ms) t-sub0))) pass2)))
    (define pl (car free))
    (set! free (cdr free))
    (place-channel-put pl (vector 'search lang (search-ctx-start ctx)
                                  unresolved (witness-ms) (witness-states)
                                  (add1 (search-seed lang (search-ctx-i ctx)))))
    (set! in-flight (cons (list pl ctx (- (now-ms) t1) v1) in-flight)))
  (let drain2 ()
    (unless (null? in-flight)
      (match-define (cons (and e (list pl ctx0 t-sub0 v0)) msg)
        (apply sync (for/list ([e (in-list in-flight)])
                      (wrap-evt (car e) (lambda (msg) (cons e msg))))))
      (set! in-flight (remq e in-flight))
      (set! free (cons pl free))
      (define v* (for/fold ([h v0]) ([kv (in-list msg)])
                   (hash-set h (car kv) (cadr kv))))
      (set! pass2 (cons (list ctx0 v* (round (- (now-ms) t-sub0))) pass2))
      (drain2)))
  ;; Tier 3: local search, all places as walk helpers, for any survivor.
  (for ([item (in-list (reverse pass2))])
    (match-define (list ctx v2 t2) item)
    (define unresolved (unresolved-of ctx v2))
    (cond
      [(null? unresolved) (finish-program lang st ctx v2 t2)]
      [else
       (printf "  [~a] tier 3: ~a target(s) resisted the full-budget job; pooled walk search~n"
               (search-ctx-i ctx) (length unresolved))
       (flush-output)
       (define-values (v3 t3) (local-search ctx unresolved (witness-ms) pool))
       (define merged (for/fold ([h v2]) ([(k val) (in-hash v3)]) (hash-set h k val)))
       (finish-program lang st ctx merged (+ t2 t3))]))
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
    "Concurrent program searches per lane (places), 0 = local sequential (default: 3)"
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
