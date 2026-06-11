#lang racket/base

(require racket/port
         racket/file
         racket/format
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
         compile-and-run-smol)

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

(define (compile-and-run-rust cargo-toml compile-fn e #:timeout [timeout 120])
  (define src (compile-fn e))
  (define dir (make-temp-dir))
  (make-directory (build-path dir "src"))
  (display-to-file cargo-toml (build-path dir "Cargo.toml"))
  (display-to-file src (build-path dir "src" "main.rs"))
  (begin0
    (run-command (format "cd '~a' && cargo run -q" (path->string dir))
                 #:timeout timeout)
    (delete-directory/files dir)))

(define (compile-and-run-tokio e #:timeout [timeout 120])
  (compile-and-run-rust tokio-cargo-toml compile-tokio e #:timeout timeout))

(define (compile-and-run-smol e #:timeout [timeout 120])
  (compile-and-run-rust smol-cargo-toml compile-smol e #:timeout timeout))
