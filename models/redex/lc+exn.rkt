#lang racket

(require redex "lc.rkt")

(provide LC+Exn -->exn/core -->exn)

(define-extended-language LC+Exn LC
  (e ::= ....              
     (throw e)
     (catch e_handle e_try))
  
  (E ::= ....
     (throw E)
     (catch E e)
     (catch v E))

  (G ::= 
     ;; Evaluation context `E` without a `catch` term
     (side-condition (name ctx E)
                     (false? (member 'catch (flatten (term ctx)))))))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->exn/core
  (reduction-relation
   LC+Exn #:domain (σ e)

   [--> (σ (in-hole E (in-hole G (throw v)))) 
        (σ (in-hole E (throw v)))
        
        (side-condition (not (equal? (term hole)
                                     (term G))))
        "throw"]
   
   [--> (σ (in-hole E (catch (lambda (x) e) (throw v)))) 
        (σ (in-hole E ((lambda (x) e) v)))
        "catch-exn"]

   [--> (σ (in-hole E (catch _ v)))
        (σ (in-hole E v))
        "catch-value"]))

(define -->lc/base
  (extend-reduction-relation -->lc LC+Exn))

(define -->exn
  (union-reduction-relations -->lc/base -->exn/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "lc.rkt" niceties)
           (submod "lc.rkt" test))

  (define-metafunction/extension main LC+Exn
    main/exn : e -> (σ e))
  
  (define-syntax-rule (exn-->>= e v)
    (test-->> -->exn #:equiv prog/equiv (term (main/exn e)) v))

  (test--> -->exn
           (term (() (+ 1 (+ 2 (+ 3 (+ (throw "what?") 4))))))
           (term (() (throw "what?"))))

  (test--> -->exn
           (term (() (catch (lambda (e) 0)
                            (+ 1 (+ 2 (+ 3 (+ (throw "what?") 4)))))))
           (term (() (catch (lambda (e) 0)
                            (throw "what?")))))

  (exn-->>=
   (+ 1 (catch (lambda (e) 41)
               (throw "nope")))
   42)
  
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
   (+ 0 ((lambda ()
                  (+ 1 (+ 2 (+ 3 (+ (throw "what?") 4)))))))
   (term (throw "what?")))

  (exn-->>=
   (catch (lambda (e) 0)
          (if #false
              (throw "nope")
              (+ 21 21)))
   42))