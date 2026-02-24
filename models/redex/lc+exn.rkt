#lang racket/base

(require redex/reduction-semantics
         "lc.rkt")

(provide LC+Exn -->exn/core -->exn)

(define-extended-language LC+Exn LC
  (e ::= ....
     (throw e)
     (catch e_handle e_try))

  (E ::= ....
     (throw E)
     (catch E e)
     (catch v E))

  (M ::= ....
     (throw M)
     (catch M e)
     (catch v M))

  (G ::=
     (throw G)

     ;; Copied from the base LC
     hole
     (reset G)
     (v ... G e ...)
     (fix G)
     (set! x G)
     (let ([x_0 v] ... [x G] [x_1 e] ...) e)
     (begin v ... G e ...)
     (if G e e)
     (list v ... G e ...)
     (cons G e)
     (cons v G)
     (car G)
     (cdr G)
     (empty? G)
     (struct [x_0 v] ... [x G] [x_s e] ...)
     (field x G)
     (box G)
     (unbox G)
     (set-box! G e)
     (set-box! v G)
     (+ v ... G e ...)
     (- v ... G e ...)
     (= v ... G e ...)
     (< v ... G e ...)
     (> v ... G e ...)
     (<= v ... G e ...)
     (>= v ... G e ...)
     (num->string G)

     (equal? v ... G e ...)
     (append v ... G e ...)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->exn/core
  (reduction-relation
   LC+Exn #:domain (σ e)

   [--> (σ (in-hole E (catch (lambda (x) e) (in-hole G (throw v)))))
        (σ (in-hole E ((lambda (x) e) v)))
        "catch-exn"]

   [--> (σ (in-hole G (throw v)))
        (σ (throw v))
        (side-condition (not (equal? (term hole) (term G))))
        "uncaught-exn"]

   [--> (σ (in-hole E (catch _ v)))
        (σ (in-hole E v))
        "catch-value"]))

(define -->lc/base
  (extend-reduction-relation -->lc LC+Exn))

(define -->exn
  (union-reduction-relations -->lc/base -->exn/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "lc.rkt" test/helpers)
           racket/control
           rackunit)

  (struct my-exn (payload) #:transparent)

  (define-syntax-rule (catch handler body)
    (with-handlers ([my-exn? (lambda (exn-obj)
                               (handler (my-exn-payload exn-obj)))])
      body))

  (define-syntax-rule (throw e)
    (raise (my-exn e)))

  (define-syntax-rule (eval-in-racket expr)
    (with-handlers ([my-exn? (lambda (exn-obj)
                               `(throw ,(my-exn-payload exn-obj)))])
      expr))

  (define-syntax-rule (exn-->>= e v)
    (let ([t (term (() e))]
          [expected v]
          [racket-val (eval-in-racket e)])

      ;; Check semantics against racket
      (check-equal? racket-val expected
                    (format "Racket evaluation diverged for: ~a" 'e))

      ;; Check deterministic evaluation
      (apply-reduction-relation* -->exn t #:error-on-multiple? #true)

      ;; Check output of actual test
      (test-->> -->exn #:equiv prog/equiv t expected))))

(module+ test
  (exn-->>=
   (+ 1 (catch (lambda (e) 41)
               (throw "nope")))
   42)

  (exn-->>=
   (+ 1 (catch (lambda (e) 41)
               (let ([x (throw "nope")])
                 0)))
   42)

  (exn-->>=
   (+ 0 (catch (lambda (e) 42)
               ((lambda ()
                  (begin
                    (throw "what?")
                    1)))))
   42)

  (exn-->>=
   (let ([throwing! (lambda () (throw 0))]
         [with-default (lambda (d thunk)
                         (catch (lambda (e) d)
                                (thunk)))])
     (with-default 42 throwing!))
   42)

  (exn-->>=
   (let ([thirty-eight (lambda (_e) 38)]
         [add1 (lambda (n) (+ n 1))])
     (add1 (add1 (add1 (add1 (catch thirty-eight
                                    (add1 (add1 (add1 (throw 0))))))))))
   42)

  (exn-->>=
   (+ 0 ((lambda ()
           (+ 1 (+ 2 (+ 3 (+ (throw "what?") 4)))))))
   (term (throw "what?")))

  (exn-->>=
   (catch (lambda (e) 0)
          (if #false
              (throw "nope")
              (+ 21 21)))
   42)

  (exn-->>=
   (catch (lambda (e) 42)
          (reset (+ 10 (throw "error"))))
   42)

  (exn-->>=
   (+ 10
      (reset
       (catch (lambda (e) 0) ; This handler is abandoned
              (+ 1 (shift k 32)))))
   42)

  (exn-->>=
   (catch (lambda (e) 42)          ; <-- Caught here
          (reset
           (catch (lambda (e) 0)   ; <-- Captured into `k` and ignored
                  (+ 1 (shift k (throw "error"))))))
   42)

  (exn-->>=
   (let ([k-func (reset
                  (catch (lambda (e) 42)
                         ;; Capture the application context: (catch ... ([]))
                         ((shift k k))))])
     ;; k-func is roughly: (lambda (thunk) (reset (catch ... (thunk))))
     (k-func (lambda () (throw "error"))))
   42)

  (exn-->>=
   (catch (lambda (e) 42)
          (reset
           (+ 1 (shift k
                       (+ 100 (k (throw "error")))))))
   42))
