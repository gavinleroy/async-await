#lang racket

(require redex
         "lc.rkt"
         (prefix-in lib: (submod "lc.rkt" niceties))
         "lc+coro.rkt")

(provide Rust -->rs)

(define-extended-language Rust LC+Coro
  (e ::= ....
     (async/lambda (x_!_ ...) e)
     (await e))

  (E ::= ....
     (await E))
  
  (v ::= ....
     (async/lambda (x_!_ ...) e))

  #:binding-forms

  (async/lambda (x ...) e #:refers-to (shadow x ...)))

(define -->rs
  (extend-reduction-relation
   -->coro Rust

   [--> (σ_0 (in-hole E ((async/lambda (x ...) e) v ...)))
        (σ_1 (in-hole E (coro (lambda (x_dummy)
                                (begin x_dummy e)))))

        (where x_dummy (gensym σ_0 dummy))
        (where σ_1 (ext σ_0 (x v) ...))
        "async-app"]

   [--> (σ (in-hole E (await (tag x_coro))))
        (σ (in-hole E ((lambda (x) e) (void))))

        (where/error (coroutine (lambda (x) e))
                     (lookup σ x_coro))
        "await-coro"]))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "lc.rkt" niceties)
           (submod "lc.rkt" test))

  (define-metafunction/extension main Rust
    main/rs : e -> (σ e))
  
  (define-syntax-rule (rs-->>= e v)
    (test-->> -->rs #:equiv prog/equiv (term (main/rs e)) v))
  
  (rs-->>=
   (resume! ((async/lambda (x) 42) 0) (void))
   42)
  
  (rs-->>= 
   (trace-stdout (print)
     (let* ([suspend (async/lambda () (void))]
            [work (async/lambda (msg)
                    (begin (await (suspend))
                           (print msg)))]
            [c (work "A")])
       (begin (resume! c (void))
              (resume! c (void)))))
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
       (begin (resume! c (void))
              (resume! c (void))
              (resume! c (void))
              (resume! c (void)))))
   "AAA")

  (rs-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda () (print "A"))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (resume! (resume! (transparent) (void))
                (void))))
   "BA"))