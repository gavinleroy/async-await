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
                                (lib:begin x_dummy ;; resume! value is (void)
                                       e)))))

        (where x_dummy (gensym σ_0 dummy))
        (where σ_1 (ext σ_0 (x v) ...))
        "async-app"]

   [--> (σ_0 (in-hole E (tagged x_running (in-hole E_inner (await (tag x_coro))))))
        (σ_1 (in-hole E (tag x_running)))

        (side-condition (not (term (in-tag? E_inner))))
        (where x_dummy (gensym σ_0 dummy))
        (where v_coro
               (coroutine
                (lambda (x_dummy)
                  (in-hole E_inner
                           (lib:begin x_dummy
                                  (await (resume! (tag x_coro) (void))))))))
        (where σ_1 (ext1 σ_0 (x_running v_coro)))
        "await-coro"]

   [--> (σ (in-hole E (await v)))
        (σ (in-hole E v))

        (side-condition (not (term (awaitable? v))))
        "await-continue"]))

;; -----------------------------------------------------------------------------
;; Metafunctions
;; -----------------------------------------------------------------------------

(define-metafunction Rust
  async-resume : any -> any
  [(async-resume (tag x_coro))
   (resume! (tag x_coro) (void))]
  [(async-resume (task x_task))
   (task x_task)]
  [(async-resume any)
   ,(error 'async-resume "~e is not an awaitable" (term any))])

(define-metafunction Rust
  awaitable? : any -> boolean
  [(awaitable? (tag _)) #true]
  [(awaitable? (task _)) #true]
  [(awaitable? _) #false])

(define-metafunction/extension in-tag? Rust
  in-tag?/rs : E -> boolean)

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