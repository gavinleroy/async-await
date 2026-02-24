#lang racket/base

(require redex/reduction-semantics
         "core.rkt")

(provide LC -->lc)

(define-language LC
  (e ::=
     x
     v
     (set! x e)
     (e e ...)
     (if e e e)
     (let ([x_!_ e] ...) e)
     (fix e)
     (lambda (x_!_ ...) e)
     (begin e ...+)

     (reset e)
     (shift x e)

     (ok e)
     (err e)

     (list e ...)
     (cons e e)
     (car e)
     (cdr e)
     (empty? e)

     (struct [x_!_ e] ...)
     (field x e)

     (box e)
     (unbox e)
     (set-box! e e)

     (+ e ...)
     (- e ...)
     (number->string e)
     (= e e)
     (< e e)
     (> e e)
     (<= e e)
     (>= e e)

     (equal? e e ...)
     (string-append e e ...)
     )

  (v ::=
     number
     string
     boolean
     (ptr x)
     (void)
     (fix v)
     (lambda (x_!_ ...) e)
     (list v ...)
     (struct [x_!_ v] ...))

  (E ::=
     hole
     (reset E)
     (v ... E e ...)
     (set! x E)
     (let ([x_0 v] ... [x E] [x_1 e] ...) e)
     (fix E)
     (begin v ... E e ...)
     (if E e e)

     (list v ... E e ...)
     (cons E e)
     (cons v E)
     (car E)
     (cdr E)
     (empty? E)

     (struct [x_0 v] ... [x E] [x_s e] ...)
     (field x E)

     (box E)
     (unbox E)
     (set-box! E e)
     (set-box! v E)

     (+ v ... E e ...)
     (- v ... E e ...)
     (= v ... E e ...)
     (< v ... E e ...)
     (> v ... E e ...)
     (<= v ... E e ...)
     (>= v ... E e ...)
     (number->string E)

     (equal? v ... E e ...)
     (string-append v ... E e ...)
     )

  (M ::=
     ;; Copied from above, just without `reset`
     hole
     (v ... M e ...)
     (set! x M)
     (let ([x_0 v] ... [x M] [x_1 e] ...) e)
     (fix M)
     (begin v ... M e ...)
     (if M e e)
     (list v ... M e ...)
     (cons M e)
     (cons v M)
     (car M)
     (cdr M)
     (empty? M)
     (struct [x_0 v] ... [x M] [x_s e] ...)
     (field x M)
     (box M)
     (unbox M)
     (set-box! M e)
     (set-box! v M)
     (+ v ... M e ...)
     (- v ... M e ...)
     (= v ... M e ...)
     (< v ... M e ...)
     (> v ... M e ...)
     (<= v ... M e ...)
     (>= v ... M e ...)
     (number->string M)
     (equal? v ... M e ...)
     (string-append v ... M e ...))

  (σ ::= ((x v) ...))

  (x ::= variable-not-otherwise-mentioned)

  #:binding-forms

  (lambda (x ...) e #:refers-to (shadow x ...))
  (let ([x e] ...) e_body #:refers-to (shadow x ...))
  (shift x e #:refers-to (shadow x)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->lc/core
  (reduction-relation
   LC
   #:domain (σ e)

   [--> (σ (in-hole E x))
        (σ (in-hole E v))

        (where v (lookup σ x))
        "var"]

   [--> (σ (in-hole E (if #false e_1 e_2)))
        (σ (in-hole E e_2))
        "if-false"]

   [--> (σ (in-hole E (if v e_1 e_2)))
        (σ (in-hole E e_1))

        (side-condition (not (equal? #false (term v))))
        "if-true"]

   [--> (σ (in-hole E ((fix v_rec) v_arg ...)))
        (σ (in-hole E ((v_rec (fix v_rec)) v_arg ...)))

        (where (lambda (x ...) e) v_rec)
        "fix"]

   [--> (σ_0 (in-hole E ((lambda (x ..._1) e) v ..._1)))
        (σ_1 (in-hole E e_subst))

        (where/error (x_fresh ...) (gensyms (σ_0 e) (x ...)))
        (where/error σ_1 (ext σ_0 (x_fresh v) ...))
        (where/error e_subst (substitute* e (x x_fresh) ...))
        "app"]

   [--> (σ_0 (in-hole E (let ([x v] ...) e_body)))
        (σ_1 (in-hole E e_subst))

        (where/error (x_fresh ...) (gensyms (σ_0 e_body) (x ...)))
        (where/error σ_1 (ext σ_0 (x_fresh v) ...))
        (where/error e_subst (substitute* e_body (x x_fresh) ...))
        "let"]

   [--> (σ_0 (in-hole E (set! x v)))
        (σ_1 (in-hole E (void)))

        (where/error σ_1 (ext1 σ_0 (x v)))
        "set!"]

   [--> (σ (in-hole E (begin v ... v_final)))
        (σ (in-hole E v_final))
        "begin"]))


(define -->lc/delim-ks
  (reduction-relation
   LC
   #:domain (σ e)

   [--> (σ (in-hole E (reset v)))
        (σ (in-hole E v))
        "reset-val"]

   [--> (σ_0 (in-hole E (reset (in-hole M (shift x_k e)))))
        (σ_1 (in-hole E (reset e_subst)))

        (where/error (x_fresh x_called) (gensyms (σ_0 e) (x_k x_k)))
        (where/error σ_1 (ext1 σ_0 (x_fresh (lambda (x_called)
                                              (reset (in-hole M x_called))))))
        (where/error e_subst (substitute*  e (x_k x_fresh)))
        "shift"]))


(define -->lc/struct
  (reduction-relation
   LC
   #:domain (σ e)

   [--> (σ (in-hole E (field x_field v_struct)))
        (σ (in-hole E v))

        (where/error (struct [x_s v_s] ...) v_struct)
        (where/error v (lookup ((x_s v_s) ...) x_field))
        "field"]))

(define -->lc/list
  (reduction-relation
   LC
   #:domain (σ e)

   [--> (σ (in-hole E (empty? (list))))
        (σ (in-hole E #true))
        "empty?-true"]

   [--> (σ (in-hole E (empty? (list v v_rest ...))))
        (σ (in-hole E #false))
        "empty?-false"]

   [--> (σ (in-hole E (car (list v_0 v...))))
        (σ (in-hole E v_0))
        "car"]

   [--> (σ (in-hole E (cdr (list v_0 v...))))
        (σ (in-hole E (list v...)))
        "cdr"]

   [--> (σ (in-hole E (cons v_new (list v ...))))
        (σ (in-hole E (list v_new v ...)))
        "cons"]))


(define -->lc/box
  (reduction-relation
   LC
   #:domain (σ e)

   [--> (σ_0 (name prog (in-hole E (box v))))
        (σ_1 (in-hole E (ptr x)))

        (where/error (ptr x) (malloc σ_0))
        (where/error σ_1 (ext1 σ_0 (x v)))
        "box"]

   [--> (σ (in-hole E (unbox v)))
        (σ (in-hole E v_unboxed))

        (where/error (ptr x) v)
        (where/error v_unboxed (lookup σ x))
        "unbox"]

   [--> (σ_0 (in-hole E (set-box! v_ptr v_new)))
        (σ_1 (in-hole E (void)))

        (where/error (ptr x_addr) v_ptr)
        (where/error σ_1 (ext1 σ_0 (x_addr v_new)))
        "set-box!"]))


(define -->lc/num
  (reduction-relation
   LC
   #:domain (σ e)

   [--> (σ (in-hole E (+ number ...)))
        (σ (in-hole E ,(apply + (term (number ...)))))
        "add"]

   [--> (σ (in-hole E (- number ...)))
        (σ (in-hole E ,(apply - (term (number ...)))))
        "subtract"]

   [--> (σ (in-hole E (number->string number)))
        (σ (in-hole E ,(number->string (term number))))
        "number->string"]

   [--> (σ (in-hole E (= number ...)))
        (σ (in-hole E ,(apply = (term (number ...)))))
        "num="]

   [--> (σ (in-hole E (< number ...)))
        (σ (in-hole E ,(apply < (term (number ...)))))
        "num<"]

   [--> (σ (in-hole E (> number ...)))
        (σ (in-hole E ,(apply > (term (number ...)))))
        "num>"]

   [--> (σ (in-hole E (<= number ...)))
        (σ (in-hole E ,(apply <= (term (number ...)))))
        "num<="]

   [--> (σ (in-hole E (>= number ...)))
        (σ (in-hole E ,(apply >= (term (number ...)))))
        "num>="]))


(define -->lc/string
  (reduction-relation
   LC
   #:domain (σ e)

   [--> (σ (in-hole E (string-append string ...)))
        (σ (in-hole E ,(apply string-append (term (string ...)))))
        "string-append"]

   [--> (σ (in-hole E (equal? string ...)))
        (σ (in-hole E ,(apply equal? (term (string ...)))))
        "string="]))


(define -->lc
  (union-reduction-relations
   -->lc/core
   -->lc/box
   -->lc/delim-ks
   -->lc/struct
   -->lc/list
   -->lc/num
   -->lc/string
   ))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test/helpers
  (require racket/match)
  (provide final-value prog/equiv)

  (define (final-value p)
    (match p
      [`(,_σ ,v) v]
      [_ p]))

  (define (prog/equiv p v)
    ((default-equiv)
     (final-value p)
     v)))

(module+ test
  (require (submod ".." test/helpers)
           (submod "core.rkt" niceties)
           #;racket/control
           #;rackunit)

  ;; TODO, define macros for the niceties lib and then run things in racket
  (define-syntax-rule (eval-in-racket e)
    (let-syntax ()
      (void)
      #;e))

  (define-syntax-rule (lc-->>= e v)
    (let ([t (term (() e))]
          [expected v]
          [racket-val (eval-in-racket e)])
      (begin
        ;(check-equal? racket-val expected (format "Racket evaluation diverged for: ~a" 'e))
        (apply-reduction-relation* -->lc t #:error-on-multiple? #true)
        (test-->> -->lc #:equiv prog/equiv t v)))))

(module+ test
  (lc-->>=
   (+ 21 21)
   42)

  (lc-->>=
   (- 42 0)
   42)

  (lc-->>=
   (- 42 42)
   0)

  (lc-->>=
   (- 42 42 42)
   -42)

  (lc-->>=
   (if (= 0 0) 42 21)
   42)

  (lc-->>=
   (if (equal? "a" "b") 42 21)
   21)

  (lc-->>=
   (if (equal? "a" "a") 42 21)
   42)

  (lc-->>=
   (+ 1 (reset (+ 10 (shift k 1))))
   2)

  (lc-->>=
   (+ 1 (reset (+ 10
                  (shift k
                         (+ 3 (k 5))))))
   19)

  (lc-->>=
   (let ([x 1])
     (let ([f (lambda (y) x)])
       (let ([x 42])
         (f 0))))
   1)

  (lc-->>=
   (let ([counter 42]
         [times 0])
     (letrec ([loop (lambda ()
                      (if (< 0 counter)
                          (begin (set! counter (- counter 1))
                                 (set! times (+ times 1))
                                 (loop))
                          (void)))])
       (begin (loop) times)))

   42)

  (lc-->>=
   ((lambda (x) x) 42)
   42)

  (lc-->>=
   (let* ([x 21]
          [y (+ x 10)]
          [z (+ y 11)])
     z)
   42)

  (lc-->>=
   (let ([x 0] [y 42])
     (let ([y x] [x y])
       x))
   42)

  (lc-->>=
   (let* ([x 42]
          [c 0])
     (letrec ([loop (lambda ()
                      (if (= 0 x)
                          (void)
                          (begin
                            (set! c (+ c 1))
                            (set! x (+ x -1))
                            (loop))))])
       (begin (loop) c)))
   42)

  (lc-->>=
   (let* ([x 42]
          [c 0])
     (letrec ([loop (lambda ()
                      (if (= 0 x)
                          (void)
                          (begin
                            (set! c (+ c 1))
                            (set! x (+ x -1))
                            (loop))))])
       (begin (loop) c)))
   42)

  (lc-->>=
   (let* ([x 42]
          [foo (lambda (x) (set! x 100))])
     (begin (foo x) x))
   42)

  (lc-->>=
   (let* ([x 0]
          [x (begin (set! x 1) (+ x 1))]
          [x (+ x 1)]
          [x (+ x 39)])
     x)
   42)

  (lc-->>=
   (string-append (number->string 4) (number->string 2))
   "42")

  (lc-->>=
   (let* ([x 10] [c ""])
     (letrec ([loop (lambda ()
                      (if (= 0 x)
                          (void)
                          (begin
                            (set! x (+ x -1))
                            (set! c (string-append c (number->string  x)))
                            (loop))))])
       (begin (loop) c)))
   "9876543210")

  (lc-->>=
   (let* ([x 10] [c (box "")])
     (letrec ([loop (lambda ()
                      (if (= 0 x)
                          (void)
                          (begin
                            (set! x (+ x -1))
                            (set-box! c (string-append (unbox c) (number->string  x)))
                            (loop))))])
       (begin (loop) (unbox c))))
   "9876543210")

  (lc-->>=
   (field x (struct [x 42] [y 0]))
   42)

  (lc-->>=
   (let ([s (struct [x (- 42 21)] [y 21])])
     (+ (field x s)
        (field y s)))
   42)

  (lc-->>=
   (trace-stdout (print)
     (print "hello")
     (print ", world"))
   "hello, world"))
