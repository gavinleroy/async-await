#lang racket

(require racket/control)

(struct my-exception exn:fail:user ())

(define-syntax-rule (catch handler body)
  (with-handlers ([my-exception? handler])
    body))

(define-syntax-rule (throw e)
  (raise (my-exception e (current-continuation-marks))))


(catch (lambda (e) 42)
       (reset (+ 10 (throw "error"))))
