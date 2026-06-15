#lang racket/base

(require racket/port
         racket/file
         racket/format
         racket/match
         "compile-js.rkt"
         "compile-py.rkt"
         "compile-cs.rkt"
         "compile-swift.rkt"
         "compile-rs.rkt")

(provide (struct-out run-result)
         compile-and-run-js
         compile-and-run-asyncio
         compile-and-run-trio
         compile-and-run-cs
         compile-and-run-swift
         compile-and-run-tokio
         compile-and-run-smol
         compile-and-run-many)

(struct run-result (exit-code stdout stderr) #:transparent)

;; ---------------------------------------------------------------------------
;; Subprocess helpers
;; ---------------------------------------------------------------------------

(define (run-command cmd #:timeout [timeout 30])
  (define-values (sp out in err)
    (subprocess #f #f #f "/bin/sh" "-c" cmd))
  (close-output-port in)
  (define done (sync/timeout timeout sp))
  (cond
    [done
     (define stdout-str (port->string out))
     (define stderr-str (port->string err))
     (close-input-port out)
     (close-input-port err)
     (run-result (subprocess-status sp) stdout-str stderr-str)]
    [else
     (subprocess-kill sp #t)
     (close-input-port out)
     (close-input-port err)
     (run-result 'timeout "" "timed out")]))

(define (make-temp-dir)
  (define tmp (make-temporary-file "gen~a"))
  (delete-file tmp)
  (make-directory tmp)
  tmp)

;; ---------------------------------------------------------------------------
;; JavaScript — node
;; ---------------------------------------------------------------------------

(define (compile-and-run-js e #:timeout [timeout 30])
  (define src (compile-js e))
  (define tmp (make-temporary-file "gen~a.js"))
  (display-to-file src tmp #:exists 'replace)
  (begin0
    (run-command (format "node '~a'" (path->string tmp)) #:timeout timeout)
    (delete-file tmp)))

;; ---------------------------------------------------------------------------
;; Python — asyncio / trio
;; ---------------------------------------------------------------------------

(define (compile-and-run-asyncio e #:timeout [timeout 30])
  (define src (compile-asyncio e))
  (define tmp (make-temporary-file "gen~a.py"))
  (display-to-file src tmp #:exists 'replace)
  (begin0
    (run-command (format "python3 '~a'" (path->string tmp)) #:timeout timeout)
    (delete-file tmp)))

(define (compile-and-run-trio e #:timeout [timeout 30])
  (define src (compile-trio e))
  (define tmp (make-temporary-file "gen~a.py"))
  (display-to-file src tmp #:exists 'replace)
  (begin0
    (run-command (format "python3 '~a'" (path->string tmp)) #:timeout timeout)
    (delete-file tmp)))

;; ---------------------------------------------------------------------------
;; C# — dotnet run
;; ---------------------------------------------------------------------------

(define csproj-content #<<EOF
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <OutputType>Exe</OutputType>
    <TargetFramework>net10.0</TargetFramework>
  </PropertyGroup>
</Project>
EOF
)

(define (compile-and-run-cs e #:timeout [timeout 60])
  (define src (compile-cs e))
  (define dir (make-temp-dir))
  (display-to-file csproj-content (build-path dir "generated.csproj") #:exists 'replace)
  (display-to-file src (build-path dir "Program.cs") #:exists 'replace)
  (begin0
    (run-command (format "dotnet run --project '~a'" (path->string dir))
                 #:timeout timeout)
    (delete-directory/files dir)))

;; ---------------------------------------------------------------------------
;; Swift — swiftc + run
;; ---------------------------------------------------------------------------

(define (compile-and-run-swift e #:timeout [timeout 60])
  (define src (compile-swift e))
  (define dir (make-temp-dir))
  (define src-file (build-path dir "main.swift"))
  (define bin-file (build-path dir "main"))
  (display-to-file src src-file)
  (begin0
    (run-command
     (format "swiftc -swift-version 6 -parse-as-library '~a' -o '~a' && '~a'"
             (path->string src-file)
             (path->string bin-file)
             (path->string bin-file))
     #:timeout timeout)
    (delete-directory/files dir)))

;; ---------------------------------------------------------------------------
;; Rust — cargo run (tokio / smol)
;; ---------------------------------------------------------------------------

(define tokio-cargo-toml #<<EOF
[package]
name = "generated"
version = "0.1.0"
edition = "2021"

[dependencies]
tokio = { version = "=1.50.0", features = ["full"] }
EOF
)

(define smol-cargo-toml #<<EOF
[package]
name = "generated"
version = "0.1.0"
edition = "2021"

[dependencies]
smol = "=2.0.2"
EOF
)

;; When ASYNC_FUZZ_CARGO_CONFIG is set (the Nix shell points it at a cargo
;; config with vendored sources), builds run fully offline.
(define (compile-and-run-rust cargo-toml compile-fn e #:timeout [timeout 120])
  (define src (compile-fn e))
  (define dir (make-temp-dir))
  (define cargo-config (getenv "ASYNC_FUZZ_CARGO_CONFIG"))
  (make-directory (build-path dir "src"))
  (display-to-file cargo-toml (build-path dir "Cargo.toml"))
  (display-to-file src (build-path dir "src" "main.rs"))
  (when cargo-config
    (make-directory (build-path dir ".cargo"))
    (copy-file cargo-config (build-path dir ".cargo" "config.toml")))
  (begin0
    (run-command (format "cd '~a' && cargo run -q~a"
                         (path->string dir)
                         (if cargo-config " --offline" ""))
                 #:timeout timeout)
    (delete-directory/files dir)))

(define (compile-and-run-tokio e #:timeout [timeout 120])
  (compile-and-run-rust tokio-cargo-toml compile-tokio e #:timeout timeout))

(define (compile-and-run-smol e #:timeout [timeout 120])
  (compile-and-run-rust smol-cargo-toml compile-smol e #:timeout timeout))

;; ---------------------------------------------------------------------------
;; Multi-run execution: compile once, run n times
;; ---------------------------------------------------------------------------

;; Nondeterministic programs are sampled by running the same compiled
;; artifact repeatedly; building once matters for the compiled backends
;; (dotnet/swiftc/cargo). Returns a list of run-results — a single failed
;; result when the one-time build fails.
(define (compile-and-run-many lang e n #:timeout [timeout 30])
  (define (interpreted src-of ext runner)
    (define tmp (make-temporary-file (string-append "gen~a" ext)))
    (display-to-file (src-of e) tmp #:exists 'replace)
    (begin0
      (for/list ([_ (in-range n)])
        (run-command (format runner (path->string tmp)) #:timeout timeout))
      (delete-file tmp)))

  ;; build once (long timeout); on success run `exec` n times
  (define (compiled setup! exec-cmd cleanup!)
    (define build (setup!))
    (begin0
      (if (and (not (eq? (run-result-exit-code build) 'timeout))
               (zero? (run-result-exit-code build)))
          (for/list ([_ (in-range n)])
            (run-command exec-cmd #:timeout timeout))
          (list build))
      (cleanup!)))

  (match lang
    ['asyncio    (interpreted compile-asyncio ".py" "python3 '~a'")]
    ['trio       (interpreted compile-trio    ".py" "python3 '~a'")]
    ['javascript (interpreted compile-js      ".js" "node '~a'")]

    ['csharp
     (define dir (make-temp-dir))
     (display-to-file csproj-content (build-path dir "generated.csproj") #:exists 'replace)
     (display-to-file (compile-cs e) (build-path dir "Program.cs") #:exists 'replace)
     (compiled
      (lambda () (run-command (format "dotnet build -v q '~a'" (path->string dir))
                              #:timeout 120))
      (format "dotnet run --no-build --project '~a'" (path->string dir))
      (lambda () (delete-directory/files dir)))]

    ['swift
     (define dir (make-temp-dir))
     (define src-file (build-path dir "main.swift"))
     (define bin-file (build-path dir "main"))
     (display-to-file (compile-swift e) src-file)
     (compiled
      (lambda () (run-command (format "swiftc -swift-version 6 -parse-as-library '~a' -o '~a'"
                                      (path->string src-file) (path->string bin-file))
                              #:timeout 120))
      (format "'~a'" (path->string bin-file))
      (lambda () (delete-directory/files dir)))]

    [(or 'tokio 'smol)
     (define dir (make-temp-dir))
     (define cargo-config (getenv "ASYNC_FUZZ_CARGO_CONFIG"))
     (make-directory (build-path dir "src"))
     (display-to-file (if (eq? lang 'tokio) tokio-cargo-toml smol-cargo-toml)
                      (build-path dir "Cargo.toml"))
     (display-to-file ((if (eq? lang 'tokio) compile-tokio compile-smol) e)
                      (build-path dir "src" "main.rs"))
     (when cargo-config
       (make-directory (build-path dir ".cargo"))
       (copy-file cargo-config (build-path dir ".cargo" "config.toml")))
     (compiled
      (lambda () (run-command (format "cd '~a' && cargo build -q~a"
                                      (path->string dir)
                                      (if cargo-config " --offline" ""))
                              #:timeout 300))
      (format "'~a'" (path->string (build-path dir "target" "debug" "generated")))
      (lambda () (delete-directory/files dir)))]

    [_ (error 'compile-and-run-many "unknown language: ~a" lang)]))
