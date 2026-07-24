#lang racket/base

(require redex/reduction-semantics
         "core.rkt"
         (only-in "exn.rkt" Exn -->exn))

(provide Py -->py/core -->py)

(define-extended-language Py Exn
  (e ::= ....
     (async/lambda (x_!_ ...) e)
     (await e))

  (v ::= ....
     (async/lambda (x_!_ ...) e))

  (E ::= .... (await E))
  (M ::= .... (await M))
  (G ::= .... (await G)))

;; No #:binding-forms: async/lambda elimination gensym-renames its parameters
;; against the whole (store, body); rationale in lc.rkt.

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->py/core
  (reduction-relation
   Py
   #:domain (σ e)

   [--> (σ_0 (in-hole E ((async/lambda (x ..._1) e_body) v ..._1)))
        (σ_1 (in-hole E (reset (begin (shift k k) e_subst))))

        ;; freshness must include the store σ_0: ext1 replaces on key
        ;; collision, so a colliding fresh name would corrupt a live binding
        (where/error (x_fresh ...) (gensyms (σ_0 e_body) (x ...)))
        (where/error σ_1 (ext σ_0 (x_fresh v) ...))
        (where/error e_subst (substitute* e_body (x x_fresh) ...))
        "async-app"]

   [--> (σ (in-hole E (await (lambda (x) (reset (begin x e))))))
        (σ (in-hole E e))

        "await-coroutine"]))

(define -->py
  (union-reduction-relations
   (extend-reduction-relation -->exn Py)
   -->py/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "core.rkt" niceties)
           (submod "lc.rkt" test/helpers))

  (define-syntax-rule (py-->>= e v)
    (test-->> -->py #:equiv prog/equiv (term (() e)) v)))

(module+ test

  ;; applying a coroutine resumes it with the given value
  (py-->>=
   (((async/lambda (x) 42) 0) (void))
   42)

  (py-->>=
   (trace-stdout (print)
     (let* ([suspend (async/lambda () (void))]
            [work (async/lambda (msg)
                    (begin (await (suspend))
                           (print msg)))]
            [c (work "A")])
       (c (void))))
   "A")

  (py-->>=
   (let* ([work (async/lambda () (throw 0))]
          [main (async/lambda ()
                  (await (work)))])
     (catch (lambda (e) "cancelled")
            ((main) (void))))
   "cancelled")

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
       (c (void))))
   "AAA")

  (py-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda () (print "A"))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (((transparent) (void)) (void))))
   "BA")

  (py-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda ()
                         (catch (lambda (e) (print e))
                                (print "A")))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (catch (lambda (e) (print "D"))
              (throw-in ((transparent) (void)) "C"))))
   "BD")

  (py-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda ()
                         (catch (lambda (e) (print e))
                                (print "A")))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (catch (lambda (e) (print "D"))
              (throw-in ((transparent) (void)) "C"))))
   "BD"))
