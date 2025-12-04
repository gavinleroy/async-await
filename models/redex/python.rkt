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
     (block e)
     (throw-in e e))

  (E ::= ....
     (await E)
     (block E)
     (throw-in E e)
     (throw-in v E))
  
  (v ::= ....
     (async/lambda (x_!_ ...) e))

  #:binding-forms

  (async/lambda (x ...) e #:refers-to (shadow x ...)))

(define -->py
  (extend-reduction-relation
   -->pybase Python

   [--> (H L_0 (in-hole E ((async/lambda (x ...) e) v ...)))
        (H L_1 (in-hole E (coro (lambda (x_dummy) (begin x_dummy e)))))

        (where/error (x_dummy) (gensyms e))
        (where L_1 (ext L_0 (x v) ...))
        "async-app"]

   [--> (H L_0 (in-hole E (throw-in (tag x_tag) v)))
        (H L_1 (in-hole E (throw-in (tag x_tag) v)))

        (where/error (coroutine (lambda (x) (in-hole E_coro x))) (lookup L_0 x_tag))
        (where L_1 (ext1 L_0 (x_tag (coroutine (lambda (x) (in-hole E_coro (throw v)))))))
        "throw-in"]

   ;; Awaiting inside an async lambda

   [--> (H L_0 (in-hole E (tagged x_tag (in-hole E_inner (await (tag x_label))))))
        (H L_1 (in-hole E (tag x_tag)))

        (side-condition (not (term (in-tag? E_inner))))
        (where (x_dummy) (gensyms (void)))
        (where L_1 (ext1 L_0 (x_tag (coroutine
                                     (lambda (x_dummy)
                                       (in-hole E_inner
                                                (await (resume! (tag x_label) (void)))))))))
        "await-pending"]

   [--> (H L (in-hole E (await v)))
        (H L (in-hole E v))

        (side-condition (not (term (awaitable? v))))
        "await-continue"]

   [--> (H L (in-hole E (block (tag x_label))))
        (H L (in-hole E (block (resume! (tag x_label) (void)))))
        "block"]

   [--> (H L (in-hole E (block v)))
        (H L (in-hole E v))

        (side-condition (not (tag? (term v))))
        "unblock"]))

;; -----------------------------------------------------------------------------
;; Metafunctions
;; -----------------------------------------------------------------------------

(define-metafunction Python
  awaitable? : any -> boolean
  [(awaitable? (tag _)) #true]
  [(awaitable? (task _ ...)) #true] ;; FIXME, this is not right
  [(awaitable? _) #false])

(define-metafunction/extension in-tag? Python
  in-tag?/py : E -> boolean)

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "lc.rkt" test))

  (define-metafunction/extension main Python
    main/py : e -> (H L e))
  
  (define-syntax-rule (py-->>= e v)
    (test-->> -->py #:equiv prog/equiv (term (main/py e)) v))
  
  (py-->>=
   (block ((async/lambda (x) 42) 0))
   42)

  (py-->>= 
   (trace-stdout (print)
                 (let* ([suspend (async/lambda () (void))]
                        [work (async/lambda (msg)
                                            (begin (await (suspend))
                                                   (print msg)
                                                   (await (suspend))
                                                   (print msg)
                                                   (await (suspend))
                                                   (print msg)))])
                   (block (work "A"))))
   "AAA")

  (py-->>=
   (trace-stdout (print)
                 (let* ([append-it (async/lambda () (print "A"))]
                        [transparent (async/lambda ()
                                                   (let ([ret (append-it)])
                                                     (begin (print "B") ret)))])
                   (block (block (transparent)))))
   "BA")
  
  (py-->>= 
   (trace-stdout (print)
                 (let* ([suspend (async/lambda () (void))]
                        [work (async/lambda (msg)
                                            (begin (await (suspend))
                                                   (print msg)))]
                        [task0 (work "A")]
                        [task1 (work "B")])
                   (begin
                     (print "C")
                     (block task0)
                     (block task1))))
   "CAB"))