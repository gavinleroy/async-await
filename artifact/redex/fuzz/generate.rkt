#lang racket/base

(require redex/reduction-semantics
         racket/match
         (only-in racket/list make-list)
         "../platform.rkt"
         "../aio.rkt"
         "../tokio.rkt"
         "../trio.rkt"
         "../smol.rkt"
         "../javascript.rkt"
         "../swift.rkt"
         "../csharp.rkt"
         "../typecheck.rkt")

(provide generate generate-expr generate-typed-expr)

;; ---------------------------------------------------------------------------

;; Forms a generated program may not use. `shift`/`reset` are
;; model-internal; bare `lambda`s are synchronous code that the async
;; runtimes cannot faithfully express (e.g. `await` inside a sync
;; function is illegal in Python/JS/C#). Extend as needed.
(define disallowed-heads '(lambda shift reset))

(define (uses-disallowed-form? t)
  (and (pair? t)
       (or (memq (car t) disallowed-heads)
           (ormap uses-disallowed-form? t))))

(define (wrap-program e threads)
  `(0 () () () ((thread (root ,e)) ,@(make-list threads '(thread)))))

(define-syntax-rule (make-generator Lang)
  (lambda (size attempts)
    (let loop ([n attempts])
      (when (zero? n)
        (error 'generate "could not generate allowed term after ~a attempts" attempts))
      (define t (generate-term Lang e size))
      (if (uses-disallowed-form? t)
          (loop (sub1 n))
          t))))

(define gen-asyncio (make-generator AsyncIO))
(define gen-tokio   (make-generator Tokio))
(define gen-trio    (make-generator Trio))
(define gen-smol    (make-generator Smol))
(define gen-js      (make-generator Js))
(define gen-swift   (make-generator Swift))
(define gen-c#      (make-generator C#))

(define generators
  (hasheq 'asyncio    gen-asyncio
          'tokio      gen-tokio
          'trio       gen-trio
          'smol       gen-smol
          'javascript gen-js
          'swift      gen-swift
          'csharp     gen-c#))

(define reducers
  (hasheq 'asyncio    -->aio
          'tokio      -->tokio
          'trio       -->trio
          'smol       -->smol
          'javascript -->js
          'swift      -->swift
          'csharp     -->c#))

(define (generate-expr lang
                       #:size [size 5]
                       #:attempts [attempts 100])
  (define gen (hash-ref generators lang
                        (lambda () (error 'generate "unknown language: ~a" lang))))
  (gen size attempts))

;; Generate until the term type-checks: only well-typed programs are
;; worth running, since they are the ones expected to run to completion.
;; Returns the raw term (for the model), its annotated form (for the
;; compilers), and its type.
(define (generate-typed-expr lang
                             #:size [size 5]
                             #:attempts [attempts 500])
  (define gen (hash-ref generators lang
                        (lambda () (error 'generate "unknown language: ~a" lang))))
  (let loop ([n attempts])
    (when (zero? n)
      (error 'generate-typed-expr "no well-typed term after ~a attempts" attempts))
    (define e (gen size 100))
    (define-values (ann type) (type-check e))
    (if ann
        (values e ann type)
        (loop (sub1 n)))))

(define (generate lang
                  #:size [size 5]
                  #:threads [threads 2]
                  #:attempts [attempts 100])
  (wrap-program (generate-expr lang #:size size #:attempts attempts) threads))

;; ---------------------------------------------------------------------------

(module+ test
  (require rackunit)

  (define ITERATIONS 50)
  (define MAX-STEPS 500)

  (define languages '(asyncio tokio trio smol javascript swift csharp))

  (for ([lang (in-list languages)])
    (printf "--- ~a ---~n" lang)
    (define red (hash-ref reducers lang))
    (define stuck 0)
    (define completed 0)
    (define capped 0)
    (define errors 0)
    (for ([i (in-range ITERATIONS)])
      (with-handlers ([exn:fail? (lambda (e)
                                   (set! errors (add1 errors))
                                   (eprintf "  [~a] error: ~a~n" i (exn-message e)))])
        (define prog (generate lang #:size 3))
        (define result (reduce red prog #:max-steps MAX-STEPS))
        (cond
          [(not result) (set! stuck (add1 stuck))]
          [else (set! completed (add1 completed))])))
    (printf "  completed: ~a  stuck: ~a  errors: ~a  (of ~a)~n"
            completed stuck errors ITERATIONS)))
