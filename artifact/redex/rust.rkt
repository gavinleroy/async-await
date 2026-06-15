#lang racket/base

(require redex/reduction-semantics
         "core.rkt"
         (only-in "lc.rkt" LC -->lc))

(provide Rust -->rs/core -->rs)

(define-extended-language Rust LC
  (e ::= ....
     (async/lambda (x_!_ ...) e)
     (await e))

  (v ::= ....
     (async/lambda (x_!_ ...) e))

  (E ::= .... (await E))
  (M ::= .... (await M))

  #:binding-forms
  (async/lambda (x ...) e #:refers-to (shadow x ...)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->rs/core
  (reduction-relation
   Rust
   #:domain (σ e)

   [--> (σ_0 (in-hole E ((async/lambda (x ..._1) e_body) v ..._1)))
        (σ_1 (in-hole E (reset (begin (shift x_k x_k) e_subst))))

        (where/error (x_fresh ...) (gensyms (σ e_body) (x ...)))
        (where/error σ_1 (ext σ_0 (x_fresh v) ...))
        (where/error e_subst (substitute* e_body (x x_fresh) ...))
        "async-app"]

   [--> (σ (in-hole E (await (lambda (x) (reset (begin x e))))))
        (σ (in-hole E e))

        "await-coroutine"]))

(define -->rs
  (union-reduction-relations
   (extend-reduction-relation -->lc Rust)
   -->rs/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "core.rkt" niceties)
           (submod "lc.rkt" test/helpers))

  (define-syntax-rule (rs-->>= e v)
    (test-->> -->rs #:equiv prog/equiv (term (() e)) v)))

(module+ test
  ;; applying a coroutine resumes it with the given value
  (rs-->>=
   (((async/lambda (x) 42) 0) (void))
   42)

  (rs-->>=
   (trace-stdout (print)
     (let* ([suspend (async/lambda () (void))]
            [work (async/lambda (msg)
                    (begin (await (suspend))
                           (print msg)))]
            [c (work "A")])
       (c (void))))
   "A")

  (rs-->>=
   (trace-stdout (print)
     (let* ([suspend (async/lambda () (void))]
            [work (async/lambda (msg)
                    (begin (await (suspend))
                           (print msg)
                           (await (suspend))
                           (print msg)
                           (await (suspend))
                           (print msg)))]
            [c (work "A")])
       (c (void))))
   "AAA")

  (rs-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda () (print "A"))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (((transparent) (void)) (void))))
   "BA"))
