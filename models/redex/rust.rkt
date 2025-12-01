#lang racket

(require redex
         "lc+coro.rkt")

(define-extended-language Rust LC+Coro
  (e ::= ....
     (async/lambda (x_!_ ...) e)
     (await e))
  
  (v ::= ....
     (async/lambda (x_!_ ...) e))
  
  (E ::= ....
     (await E))

  #:binding-forms
  
  (async/lambda (x ...) e #:refers-to (shadow x ...)))

(define -->rust
  (extend-reduction-relation
   -->coro
   Rust

   [--> (H (stack (frame L_0 (in-hole E ((async/lambda (x ..._1) e) v ..._1)) l) F ...))
        (H (stack (in-hole E (coro (lambda (_)
                                     (let ([x v] ...) e)))) F ...))
        "async-app"]

   [--> #;(H (stack (name current-frame (frame L (in-hole E (await (task o))) l)) F ...))
        #;(H (stack F ...))

        
        "await"]))

