#lang racket/base

;; -----------------------------------------------------------------------------
;; Figure-program runner: `nix run .#figs` (or `racket fuzz/figs.rkt FIGS-DIR`).
;;
;; The figs/ directory holds one subdirectory per program-bearing paper
;; figure, each containing one plain source file per language, named after
;; its fuzz lane (asyncio.py, trio.py, javascript.js, csharp.cs,
;; swift.swift, tokio.rs, smol.rs). Every file is run R times through the
;; SAME harness the fuzzer uses for generated programs (fuzz/run.rkt
;; `run-source-many`: identical temp-project shapes, pinned toolchains,
;; vendored crates), and the distinct outputs are reported — one markdown
;; table per figure, languages as rows, ready for reviewers to inspect.
;;
;; A program's printed lines are collapsed to a letter sequence ("A\nB\n" →
;; "AB"; empty output shown as ε). Nondeterministic figures (e.g. the
;; Eagerness figure's semi-eager Swift) show every distinct output with its
;; count. Placeholder files containing "TODO: paste" are reported as `todo`
;; and not run.
;; -----------------------------------------------------------------------------

(require racket/match
         racket/string
         racket/list
         racket/file
         racket/path
         racket/cmdline
         "run.rkt")

(define runs (make-parameter 5))
(define fig-filter (make-parameter '()))  ; empty = all figures
(define lang-filter (make-parameter '())) ; empty = all languages
(define ex-filter (make-parameter '()))   ; empty = all exs (tokens "ex2")

(define lane-order '(asyncio trio javascript csharp swift tokio smol))

(define (lane-of path)
  (string->symbol
   (path->string (path-replace-extension (file-name-from-path path) #""))))

(define (collapse out)
  (define letters
    (filter non-empty-string? (map string-trim (string-split out "\n"))))
  (if (null? letters) "ε" (string-join letters "")))

;; One harness invocation (= a fresh build + (runs) fresh processes), with
;; `ex` appended as the program's argument when non-#f.
;; -> (values status detail) where status ∈ ok | build-error | timeout and
;; detail is the outputs string (for ok) or a diagnostic snippet.
(define (run-one lane src lib ex)
  (define results
    (run-source-many lane src (runs) #:lib lib
                     #:run-args (if ex (list ex) '())))
  (define timeouts (filter (lambda (r) (eq? (run-result-exit-code r) 'timeout))
                           results))
  (define failures (filter (lambda (r)
                             (and (not (eq? (run-result-exit-code r) 'timeout))
                                  (not (zero? (run-result-exit-code r)))))
                           results))
  (cond
    [(pair? failures)
     (values 'build-error
             (string-trim
              (substring* (run-result-stderr (car failures)) 200)))]
    [(pair? timeouts)
     (values 'timeout (format "~a of ~a runs timed out" (length timeouts) (runs)))]
    [else
     (define counts
       (for/fold ([h (hash)]) ([r (in-list results)])
         (hash-update h (collapse (run-result-stdout r)) add1 0)))
     ;; a lone distinct output needs no count (the header carries the run
     ;; total); counts only disambiguate nondeterministic splits
     (values 'ok
             (if (= 1 (hash-count counts))
                 (format "`~a`" (car (hash-keys counts)))
                 (string-join
                  (for/list ([o (in-list (sort (hash-keys counts) string<?))])
                    (format "`~a` ×~a" o (hash-ref counts o)))
                  ", ")))]))

;; -> (values status detail). With a figure `exs` file, EACH ex runs as its
;; own fresh set of processes and the per-ex results are joined with " | ".
(define (run-figure-file path exs)
  (define lane (lane-of path))
  (define src (file->string path))
  (cond
    [(regexp-match? #rx"TODO: paste" src)
     (values 'todo (map (lambda (_) "—") exs))]
    [(not (memq lane lane-order))
     (values 'build-error
             (map (lambda (_) (format "unknown lane ~a" lane)) exs))]
    [else
     ;; Shared per-language support code (the timeout library) lives at
     ;; figs/lib/<lane>.<ext> and is bundled into the build when present.
     (define lib-path
       (simplify-path (build-path (path-only path) 'up "lib"
                                  (file-name-from-path path))))
     (define lib (and (file-exists? lib-path) (file->string lib-path)))
     (define-values (statuses details)
       (for/lists (ss ds) ([ex (in-list exs)])
         (run-one lane src lib ex)))
     (values (if (andmap (lambda (s) (eq? s 'ok)) statuses)
                 'ok
                 (string-join (map symbol->string statuses) "/"))
             details)]))

;; The optional figs/<n>/exs file lists the argument for each per-process
;; run (the ex numbers); without one the program runs bare, once.
(define (figure-exs dir)
  (define p (build-path dir "exs"))
  (define all (if (file-exists? p)
                  (string-split (file->string p))
                  (list #f)))
  (define kept (if (null? (ex-filter))
                   all
                   (filter (lambda (e) (member e (ex-filter))) all)))
  (if (null? kept) all kept))

(define (substring* s n)
  (if (<= (string-length s) n) s (substring s 0 n)))

;; Figure directories are the NUMERIC subdirectories; anything else
;; (e.g. lib/) is support material. `fig-filter` (figure numbers) narrows
;; the selection.
(define (figure-dirs root)
  (sort (for/list ([p (in-list (directory-list root #:build? #t))]
                   #:when (directory-exists? p)
                   #:when (let ([n (string->number
                                    (path->string (file-name-from-path p)))])
                            (and n
                                 (or (null? (fig-filter))
                                     (member n (fig-filter))))))
          p)
        <
        #:key (lambda (p)
                (string->number (path->string (file-name-from-path p))))))

(define (lane-files dir)
  (define by-lane
    (for/hash ([p (in-list (directory-list dir #:build? #t))]
               #:when (file-exists? p)
               #:when (memq (lane-of p) lane-order))
      (values (lane-of p) p)))
  (for/list ([lane (in-list lane-order)]
             #:when (hash-has-key? by-lane lane)
             #:when (or (null? (lang-filter)) (memq lane (lang-filter))))
    (hash-ref by-lane lane)))

(module+ main
  (define dir-arg (make-parameter #f))
  ;; Positional arguments are comma-separated FILTERS, classified by shape:
  ;; numeric tokens select figures, name tokens select languages. So
  ;; `figs 1 csharp`, `figs 1,4 csharp,tokio`, and `figs csharp` all work.
  (define filter-args
    (command-line
     #:program "figs"
     #:once-each
     [("-r" "--runs") r "Runs per program (default: 5)"
                      (runs (string->number r))]
     [("--dir") d "Figure-program directory (default: $FIGS_DIR)"
                (dir-arg d)]
     #:args filters
     filters))
  (define figs-root
    (or (dir-arg) (getenv "FIGS_DIR")
        (error 'figs "no figs directory: pass --dir or set FIGS_DIR")))
  (define tokens
    (append-map (lambda (a) (string-split a ",")) filter-args))
  (fig-filter (filter-map string->number tokens))
  (ex-filter
   (filter-map (lambda (t)
                 (define m (regexp-match #rx"^ex([0-9]+)$" t))
                 (and m (cadr m)))
               tokens))
  (lang-filter
   (for/list ([t (in-list tokens)]
              #:unless (string->number t)
              #:unless (regexp-match? #rx"^ex[0-9]+$" t))
     (define lane (string->symbol t))
     (unless (memq lane lane-order)
       (error 'figs "unknown language ~a (known: ~a)" t lane-order))
     lane))

  (for ([dir (in-list (figure-dirs figs-root))])
    (define name (path->string (file-name-from-path dir)))
    (define files (lane-files dir))
    (define exs (figure-exs dir))
    (printf "~n## Figure ~a~n~n" name)
    (cond
      [(null? files) (printf "(no programs)~n")]
      [else
       ;; one column per ex (each a fresh process), or a single outputs
       ;; column for figures without an exs file
       (define ex-headers
         (if (car exs)
             (for/list ([ex (in-list exs)])
               (format "ex~a (~a runs)" ex (runs)))
             (list (format "outputs (~a runs)" (runs)))))
       (printf "| language | status | ~a |~n" (string-join ex-headers " | "))
       (printf "|---|---|~a|~n"
               (string-join (map (lambda (_) "---") ex-headers) "|"))
       (for ([f (in-list files)])
         (define-values (status details) (run-figure-file f exs))
         (printf "| ~a | ~a | ~a |~n"
                 (lane-of f) status (string-join details " | "))
         (flush-output))]))
  (newline))
