#lang racket/base

(require redex/reduction-semantics)

(provide (all-defined-out))

(define-language REDEX)

(define-metafunction REDEX
  lookup : ((any any) ...) any -> any or not-found
  [(lookup (any_prefix ... (any any_0) _ ...) any)
   any_0
   (side-condition (not (member (term any) (term (any_prefix ...)))))]
  [(lookup any_store any_el)
   ,(error 'lookup "~e not found in store: ~e" (term any_el) (term any_store))])

(define-metafunction REDEX
  substitute* : any (variable any) ... -> any
  [(substitute* any) any]
  [(substitute* any_e (variable_0 any_0) (variable_1 any_1) ...)
   (substitute* (substitute any_e variable_0 any_0) (variable_1 any_1) ...)])

(define-metafunction REDEX
  ext1 : ((any any) ...) (any any) -> ((any any) ...)
  [(ext1 (any_0 ... (any_k any_v0) any_1 ...) (any_k any_v1))
   (any_0 ... (any_k any_v1) any_1 ...)]
  [(ext1 (any_0 ...) (any_k any_v1))
   ((any_k any_v1) any_0 ...)])

(define-metafunction REDEX
  ext : ((any any) ...) (any any) ... -> ((any any) ...)
  [(ext any) any]
  [(ext any any_0 any_1 ...)
   (ext1 (ext any any_1 ...) any_0)])

(define-metafunction REDEX
  step : natural -> natural
  [(step natural) ,(+ 1 (term natural))])

(define-metafunction REDEX
  malloc : ((any any) ...) -> any
  [(malloc any)
   (ptr (gensym any addr-))])

(define-metafunction REDEX
  gensym : any variable ... -> variable
  [(gensym any)
   ,(variable-not-in (term any) 'g)]
  [(gensym any variable)
   ,(variable-not-in (term any) (term variable))])

(define-metafunction REDEX
  gensyms : any (variable ..._1) -> (variable ..._1)
  [(gensyms any (variable ...))
   ,(variables-not-in (term any) (term (variable ...)))])

;; -----------------------------------------------------------------------------
;; Niceties, things you'll want eventually, but don't get by default
;; -----------------------------------------------------------------------------

(module+ niceties
  (require redex/reduction-semantics)

  (provide (all-defined-out))

  (define-metafunction REDEX
    and : any ... -> any
    [(and) #true]
    [(and any_0 any_s ...)
     (if any_0 (and any_s ...) #false)])

  (define-metafunction REDEX
    or : any ... -> any
    [(or) #false]
    [(or any_0 any_s ...)
     (if any_0 #true (or any_s ...))])

  (define-metafunction REDEX
    let* : ([any any] ...) any -> any
    [(let* () any) any]
    [(let* ([any_x any] [any_x_s any_s] ...) any_body)
     (let ([any_x any]) (let* ([any_x_s any_s] ...) any_body))])

  (define-metafunction REDEX
    when : any any ... -> any
    [(when any_cnd any_body ...)
     (if any_cnd
         (begin any_body ...)
         (void))])

  (define-metafunction REDEX
    letrec : ([any any]) any -> any
    [(letrec ([any_x (lambda (any_x_args ...) any_fbody)]) any_body)
     (let ([any_x (fix (lambda (any_x) (lambda (any_x_args ...) any_fbody)))])
       any_body)])

  (define-metafunction REDEX
    for-each : any any -> any
    [(for-each any_lambda any_lst)
     (letrec ([loop (lambda (lst)
                      (if (empty? lst)
                          (void)
                          (begin (any_lambda (car lst))
                                 (loop (cdr lst)))))])
       (loop any_lst))])

  (define-metafunction REDEX
    trace-stdout : (any) any ... -> any
    [(trace-stdout (any_print) any_s ...)
     (let* ([any_stdout ""]
            [any_print (lambda (s)
                         (set! any_stdout (string-append any_stdout s)))])
       (begin any_s ... any_stdout))
     (where any_stdout (gensym (any_s ...) stdout))]))
