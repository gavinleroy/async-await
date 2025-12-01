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

(define -->except
  (extend-reduction-relation
   -->sync LC+Exn
   
   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (catch v_handler (in-hole E_inner (throw v)))) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E (v_handler v)) l) F ...) FS_1 ...))

        (side-condition (not (term (in-handler? E_inner))))
        (where t_1 (step t_0))
        "catch-exception"]

   [--> (t_0 H Q (FS_0 ... (stack (frame L (in-hole E (catch v_handler v)) l) F ...) FS_1 ...))
        (t_1 H Q (FS_0 ... (stack (frame L (in-hole E v) l) F ...) FS_1 ...))

        (where t_1 (step t_0))
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
    main/exn : e -> (t H Q P)
    )
  
  (define-syntax-rule (except-->>= e v)
    (test-->> -->except #:equiv prog/equiv (term (main/exn e)) v))
  
  (except-->>=
   (+ 1 (catch (lambda (e) 41)
               (let ([x (throw "nope")])
                 0)))
   42)
  
  (except-->>=
   (+ 0 (catch (lambda (e) 42)
               ((lambda ()
                  (begin
                    (throw "what?")
                    1)))))
   42)

  (except-->>=
   (let ([throwing! (lambda () (throw 0))]
          [with-default (lambda (d thunk)
                          (catch (lambda (e) d)
                                 (thunk)))])
     (with-default 42 throwing!))
   42)

  (except-->>=
   (let ([thirty-eight (lambda (_e) 38)]
          [add1 (lambda (n) (+ n 1))])
     (add1 (add1 (add1 (add1 (catch thirty-eight
                                    (add1 (add1 (add1 (throw 0))))))))))
   42)

  (except-->>=
   (catch (lambda (e) 0)
          (if0 1
               (throw "nope")
               (+ 21 21)))
   42))