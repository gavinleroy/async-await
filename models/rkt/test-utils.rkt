#lang racket

(require "pseudo.rkt" "langs.rkt")

(provide run-test run-test*
         (all-from-out "pseudo.rkt")
         (all-from-out "langs.rkt"))

(define-syntax run-test
  (syntax-rules ()
    [(_ label with-lang entry)
     (let ()
       (define port (open-output-string))
       (define err
         (with-handlers ([exn? (lambda (e) (exn-message e))])
           (parameterize ([current-output-port port])
             (with-lang (block entry)))
           #f))
       (printf "  ~a: ~s~a~n" label
               (get-output-string port)
               (if err (format "  [ERR: ~a]" err) ""))
       (flush-output))]))

(define-syntax run-test*
  (syntax-rules ()
    [(_ label ([param val] ...) entry)
     (let ()
       (define port (open-output-string))
       (define err
         (with-handlers ([exn? (lambda (e) (exn-message e))])
           (parameterize ([current-output-port port] [param val] ...)
             (block entry))
           #f))
       (printf "  ~a: ~s~a~n" label
               (get-output-string port)
               (if err (format "  [ERR: ~a]" err) ""))
       (flush-output))]))
