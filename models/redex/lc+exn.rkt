#lang racket

(require redex "lc.rkt")

(provide (all-from-out "lc.rkt")
         (all-defined-out))

(define-extended-language LC+Exn LC
  (e ::= ....              
     (throw e)
     (catch e_handle e_try))
  
  (E ::= ....
     (throw E)
     (catch E e)
     (catch v E)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->exn
  (extend-reduction-relation
   -->lc LC+Exn
   
   [--> (H L (in-hole E (catch v_handler (in-hole E_inner (throw v))))) 
        (H L (in-hole E (v_handler v)))

        (side-condition (not (term (in-handler? E_inner))))
        "catch-exception"]

   [--> (H L (in-hole E (catch v_handler v)))
        (H L (in-hole E v))
        "catch"]))

;; -----------------------------------------------------------------------------
;; Metafunctions
;; -----------------------------------------------------------------------------

(define-metafunction LC+Exn
  in-handler? : E -> boolean
  [(in-handler? E)
   ,(not (false? (member (term catch) (flatten (term E)))))
   (side-condition (list? (term E)))]
  [(in-handler? any) #false])

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "lc.rkt" test))
  (provide (all-from-out (submod "lc.rkt" test))
           main/exn)

  (define-metafunction/extension main LC+Exn
    main/exn : e -> (H L e)
    )
  
  (define-syntax-rule (exn-->>= e v)
    (test-->> -->exn #:equiv prog/equiv (term (main/exn e)) v))
  
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
   (catch (lambda (e) 0)
          (if0 1
               (throw "nope")
               (+ 21 21)))
   42))