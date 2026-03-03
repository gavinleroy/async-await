#lang racket

(require redex
         "lc.rkt"
         (only-in "lc+exn.rkt" LC+Exn -->exn))

(provide Py -->py/core -->py)

(define-extended-language Py LC+Exn
  (e ::= ....
     (async/lambda (x_!_ ...) e)
     (await e)
     (throw-in e_coro e_exn))

  (v ::= ....
     (async/lambda (x_!_ ...) e))

  (E ::= ....
     (await E)
     (throw-in E e)
     (throw-in v E))

  (M ::= ....
     (await M)
     (throw-in M e)
     (throw-in v M))

  (G ::= ....
     (await G)
     (throw-in G e)
     (throw-in v G))

  #:binding-forms
  (async/lambda (x ...) e #:refers-to (shadow x ...)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->py/core
  (reduction-relation
   Py
   #:domain (σ e)

   [--> (σ_0 (in-hole E ((async/lambda (x ..._1) e_body) v ..._1)))
        (σ_1 (in-hole E (reset (begin (shift x_k x_k) e_subst))))

        (where/error (x_fresh ...) (gensyms (σ e_body) (x ...)))
        (where/error σ_1 (ext σ_0 (x_fresh v) ...))
        (where/error e_subst (substitute* e_body (x x_fresh) ...))
        "async-app"]

   [--> (σ (in-hole E (await (lambda (x) (reset (begin x e))))))
        (σ (in-hole E e))

        "await-coroutine"]

   [--> (σ (in-hole E (throw-in (lambda (x) (in-hold E_inner x)) v)))
        (σ (in-hole E (lambda (x) (in-hold E_inner (throw v)))))

        "throw-in"]))

(define -->py
  (union-reduction-relations
   (extend-reduction-relation -->exn Py)
   -->py/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "lc.rkt" niceties)
           (submod "lc.rkt" test/helpers))

  (define-metafunction Py
    resume! : e e -> e
    [(resume! e_coro e_val)
     (e_coro e_val)])

  (define-syntax-rule (py-->>= e v)
    (test-->> -->py #:equiv prog/equiv (term (() e)) v)))

(module+ test
  (py-->>=
   (resume! ((async/lambda (x) 42) 0) (void))
   42)

  (py-->>=
   (trace-stdout (print)
     (let* ([suspend (async/lambda () (void))]
            [work (async/lambda (msg)
                    (begin (await (suspend))
                           (print msg)))]
            [c (work "A")])
       (resume! c (void))))
   "A")

  (py-->>=
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
       (resume! c (void))))
   "AAA")

  (py-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda () (print "A"))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (resume! (resume! (transparent) (void))
                (void))))
   "BA")

  (py-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda ()
                         (catch (lambda (e) (print e))
                                (print "A")))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (throw-in (resume! (transparent) (void)) "C")))
   "B"))
