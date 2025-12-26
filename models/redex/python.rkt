#lang racket

(require redex
         "lc.rkt"
         "lc+exn.rkt"
         "lc+coro.rkt")

(provide Python -->py awaitable?)

(define-union-language PyBase
  LC+Exn LC+Coro)

(define -->lc/base
  (extend-reduction-relation -->lc PyBase))

(define -->exn/base
  (extend-reduction-relation -->exn/core PyBase))

(define -->coro/base
  (extend-reduction-relation -->coro/core PyBase))

(define -->pybase
  (union-reduction-relations -->lc/base -->exn/base -->coro/base))

(define-extended-language Python PyBase
  (e ::= ....
     (async/lambda (x_!_ ...) e)
     (await e)
     (throw-in! e e))

  (E ::= ....
     (await E)
     (throw-in! E e)
     (throw-in! v E))
  
  (v ::= ....
     (async/lambda (x_!_ ...) e))

  #:binding-forms

  (async/lambda (x ...) e #:refers-to (shadow x ...)))

(define -->py
  (extend-reduction-relation
   -->pybase Python

   [--> (σ_0 (in-hole E ((async/lambda (x ...) e) v ...)))
        (σ_1 (in-hole E (coro (lambda (x_dummy)
                                (begin x_dummy ;; resume! value is (void)
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
                           (begin x_dummy
                                  (await (resume! (tag x_coro) (void))))))))
        (where σ_1 (ext1 σ_0 (x_running v_coro)))
        "await-coro"]

   [--> (σ (in-hole E (await v)))
        (σ (in-hole E v))

        (side-condition (not (term (awaitable? v))))
        "await-continue"]

   [--> (σ_0 (in-hole E (throw-in! (tag x_tag) v)))
        (σ_1 (in-hole E (resume! (tag x_tag) (void))))

        (where/error (coroutine (lambda (x_send) (in-hole E_coro x_send)))
                     (lookup σ_0 x_tag))
        (where σ_1 (ext1 σ_0 (x_tag (coroutine (lambda (x_send) (in-hole E_coro (throw v)))))))
        "throw-in!"]))

;; -----------------------------------------------------------------------------
;; Metafunctions
;; -----------------------------------------------------------------------------

(define-metafunction Python
  async-resume : any -> any
  [(async-resume (tag x_coro))
   (resume! (tag x_coro) (void))]
  [(async-resume (task x_task))
   (task x_task)]
  [(async-resume any)
   ,(error 'async-resume "~e is not an awaitable" (term any))])

(define-metafunction Python
  awaitable? : any -> boolean
  [(awaitable? (tag _)) #true]
  [(awaitable? (task _)) #true]
  [(awaitable? _) #false])

(define-metafunction/extension in-tag? Python
  in-tag?/py : E -> boolean)

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "lc.rkt" test))

  (define-metafunction/extension main Python
    main/py : e -> (σ e))
  
  (define-syntax-rule (py-->>= e v)
    (test-->> -->py #:equiv prog/equiv (term (main/py e)) v))
  
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
       (begin (resume! c (void))
              (resume! c (void)))))
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
       (begin (resume! c (void))
              (resume! c (void))
              (resume! c (void))
              (resume! c (void)))))
   "AAA")

  (py-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda () (print "A"))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (resume! (resume! (transparent) (void))
                (void))))
   "BA"))