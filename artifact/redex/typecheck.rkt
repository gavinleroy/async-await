#lang racket/base

(require racket/match)

(provide type-check)

;; Type representation (S-expressions after zonking):
;;   Int  String  Bool  Unit
;;   (-> (τ ...) τ)
;;   (async-> (τ ...) τ)
;;   (List τ)
;;   (Box τ)
;;   (Task τ)
;;   (Struct ((name τ) ...))
;;
;; Output: typed expression where lambda/async-lambda become:
;;   (typed-lambda    (-> (τ ...) τ)       (x ...) body)
;;   (typed-async-lambda (async-> (τ ...) τ) (x ...) body)
;; All other forms unchanged structurally.

;; ---------------------------------------------------------------------------
;; Type Variables
;; ---------------------------------------------------------------------------

(struct tvar (id [link #:mutable]) #:transparent)

(define counter 0)
(define (fresh!) (set! counter (add1 counter)) (tvar counter #f))
(define (reset!) (set! counter 0))

(define (resolve t)
  (if (and (tvar? t) (tvar-link t))
      (let ([r (resolve (tvar-link t))])
        (set-tvar-link! t r) r)
      t))

;; ---------------------------------------------------------------------------
;; Occurs Check
;; ---------------------------------------------------------------------------

(define (occurs? tv t)
  (define r (resolve t))
  (cond
    [(eq? tv r) #t]
    [(tvar? r) #f]
    [else
     (match r
       [`(-> ,as ,ret)      (or (ormap (λ (a) (occurs? tv a)) as) (occurs? tv ret))]
       [`(async-> ,as ,ret) (or (ormap (λ (a) (occurs? tv a)) as) (occurs? tv ret))]
       [`(List ,t)   (occurs? tv t)]
       [`(Box ,t)    (occurs? tv t)]
       [`(Task ,t)   (occurs? tv t)]
       [`(Struct ,fs) (ormap (λ (f) (occurs? tv (cadr f))) fs)]
       [_ #f])]))

;; ---------------------------------------------------------------------------
;; Unification
;; ---------------------------------------------------------------------------

(define (unify! t1 t2)
  (define r1 (resolve t1))
  (define r2 (resolve t2))
  (cond
    [(eq? r1 r2) (void)]
    [(tvar? r1)
     (when (occurs? r1 r2) (error 'type "infinite type"))
     (set-tvar-link! r1 r2)]
    [(tvar? r2)
     (when (occurs? r2 r1) (error 'type "infinite type"))
     (set-tvar-link! r2 r1)]
    [else
     (match* (r1 r2)
       [('Int 'Int) (void)]
       [('String 'String) (void)]
       [('Bool 'Bool) (void)]
       [('Unit 'Unit) (void)]
       [(`(-> ,a1 ,r1) `(-> ,a2 ,r2))
        (unless (= (length a1) (length a2)) (error 'type "arity mismatch"))
        (for-each unify! a1 a2) (unify! r1 r2)]
       [(`(async-> ,a1 ,r1) `(async-> ,a2 ,r2))
        (unless (= (length a1) (length a2)) (error 'type "arity mismatch"))
        (for-each unify! a1 a2) (unify! r1 r2)]
       [(`(List ,a) `(List ,b)) (unify! a b)]
       [(`(Box ,a) `(Box ,b)) (unify! a b)]
       [(`(Task ,a) `(Task ,b)) (unify! a b)]
       [(`(Struct ,f1) `(Struct ,f2))
        (unless (= (length f1) (length f2)) (error 'type "struct fields"))
        (for-each (λ (a b)
                    (unless (eq? (car a) (car b)) (error 'type "struct field name"))
                    (unify! (cadr a) (cadr b)))
                  f1 f2)]
       [(_ _) (error 'type "mismatch ~a vs ~a" r1 r2)])]))

;; ---------------------------------------------------------------------------
;; Zonking (resolve all tvars → concrete types)
;; ---------------------------------------------------------------------------

(define (zonk t)
  (define r (resolve t))
  (if (tvar? r)
      'Int
      (match r
        [(or 'Int 'String 'Bool 'Unit) r]
        [`(-> ,as ,ret)      `(-> ,(map zonk as) ,(zonk ret))]
        [`(async-> ,as ,ret) `(async-> ,(map zonk as) ,(zonk ret))]
        [`(List ,t)   `(List ,(zonk t))]
        [`(Box ,t)    `(Box ,(zonk t))]
        [`(Task ,t)   `(Task ,(zonk t))]
        [`(Struct ,fs) `(Struct ,(map (λ (f) (list (car f) (zonk (cadr f)))) fs))]
        [_ (error 'zonk "unexpected: ~a" r)])))

;; Zonk type annotations inside annotated expressions
(define (zonk-expr e)
  (match e
    [`(typed-lambda ,ft ,xs ,body)
     `(typed-lambda ,(zonk ft) ,xs ,(zonk-expr body))]
    [`(typed-async-lambda ,ft ,xs ,body)
     `(typed-async-lambda ,(zonk ft) ,xs ,(zonk-expr body))]
    [`(let ,clauses ,body)
     `(let ,(map (λ (c) (list (car c) (zonk-expr (cadr c)))) clauses)
        ,(zonk-expr body))]
    [`(letrec ,clauses ,body)
     `(letrec ,(map (λ (c) (list (car c) (zonk-expr (cadr c)))) clauses)
        ,(zonk-expr body))]
    [`(set! ,x ,rhs) `(set! ,x ,(zonk-expr rhs))]
    [`(struct ,fields ...)
     `(struct ,@(map (λ (f) (list (car f) (zonk-expr (cadr f)))) fields))]
    [`(field ,name ,e) `(field ,name ,(zonk-expr e))]
    [`(: ,inner ,type) `(: ,(zonk-expr inner) ,(zonk type))]
    [(? number?) e]
    [(? string?) e]
    [(? boolean?) e]
    [(? symbol?) e]
    [(? list?) (map zonk-expr e)]
    [_ e]))

;; ---------------------------------------------------------------------------
;; Environment
;; ---------------------------------------------------------------------------

(define (lookup env x)
  (cond [(assq x env) => cdr]
        [else (error 'type "unbound: ~a" x)]))

(define (extend env x t) (cons (cons x t) env))

;; ---------------------------------------------------------------------------
;; Type Inference
;; ---------------------------------------------------------------------------

;; Wrapping layer: annotates every sub-expression with (: expr type),
;; except typed-lambda / typed-async-lambda which carry their own type.
(define (infer env e)
  (define-values (ann type) (infer-raw env e))
  (define wrapped
    (match ann
      [`(typed-lambda ,_ ...) ann]
      [`(typed-async-lambda ,_ ...) ann]
      [_ `(: ,ann ,type)]))
  (values wrapped type))

(define (infer-raw env e)
  (match e
    ;; --- Atoms ---
    [(? number?) (values e 'Int)]
    [(? string?) (values e 'String)]
    [#t (values #t 'Bool)]
    [#f (values #f 'Bool)]
    [(? symbol? x) (values x (lookup env x))]

    ;; --- Core ---
    [`(void) (values '(void) 'Unit)]
    [`(ptr ,x) (values `(ptr ,x) (lookup env x))]

    ;; --- Lambda ---
    [`(lambda (,xs ...) ,body)
     (define arg-ts (map (λ (_) (fresh!)) xs))
     (define env2 (for/fold ([e env]) ([x (in-list xs)] [t (in-list arg-ts)])
                    (extend e x t)))
     (define-values (body* bt) (infer env2 body))
     (define ft `(-> ,arg-ts ,bt))
     (values `(typed-lambda ,ft ,xs ,body*) ft)]

    [`(async/lambda (,xs ...) ,body)
     (define arg-ts (map (λ (_) (fresh!)) xs))
     (define env2 (for/fold ([e env]) ([x (in-list xs)] [t (in-list arg-ts)])
                    (extend e x t)))
     (define-values (body* bt) (infer env2 body))
     (define ft `(async-> ,arg-ts ,bt))
     (values `(typed-async-lambda ,ft ,xs ,body*) ft)]

    ;; --- Letrec ---
    [`(letrec (,clauses ...) ,body)
     (define xs (map car clauses))
     (define rhss (map cadr clauses))
     (define x-types (map (λ (_) (fresh!)) xs))
     (define env2 (for/fold ([e env]) ([x (in-list xs)] [t (in-list x-types)])
                    (extend e x t)))
     (define rhs-anns '())
     (define rhs-types '())
     (for ([r (in-list rhss)])
       (define-values (a t) (infer env2 r))
       (set! rhs-anns (append rhs-anns (list a)))
       (set! rhs-types (append rhs-types (list t))))
     (for ([xt (in-list x-types)] [rt (in-list rhs-types)])
       (unify! xt rt))
     (define-values (body* bt) (infer env2 body))
     (values `(letrec ,(map list xs rhs-anns) ,body*) bt)]

    ;; --- Let ---
    [`(let (,clauses ...) ,body)
     (define xs (map car clauses))
     (define rhss (map cadr clauses))
     (define rhs-anns '())
     (define rhs-types '())
     (for ([r (in-list rhss)])
       (define-values (a t) (infer env r))
       (set! rhs-anns (append rhs-anns (list a)))
       (set! rhs-types (append rhs-types (list t))))
     (define env2 (for/fold ([e env]) ([x (in-list xs)] [t (in-list rhs-types)])
                    (extend e x t)))
     (define-values (body* bt) (infer env2 body))
     (values `(let ,(map list xs rhs-anns) ,body*) bt)]

    ;; --- Control Flow ---
    [`(if ,c ,t ,f)
     (define-values (c* ct) (infer env c))
     (define-values (t* tt) (infer env t))
     (define-values (f* ft) (infer env f))
     (unify! ct 'Bool)
     (unify! tt ft)
     (values `(if ,c* ,t* ,f*) tt)]

    [`(begin ,es ...)
     (cond
       [(null? es) (values '(begin) 'Unit)]
       [else
        (define anns '())
        (define last-t 'Unit)
        (for ([e (in-list es)])
          (define-values (a t) (infer env e))
          (set! anns (append anns (list a)))
          (set! last-t t))
        (values `(begin ,@anns) last-t)])]

    [`(set! ,x ,rhs)
     (define xt (lookup env x))
     (define-values (r* rt) (infer env rhs))
     (unify! xt rt)
     (values `(set! ,x ,r*) rt)]

    ;; --- Arithmetic ---
    [`(+ ,es ...)
     (define anns (for/list ([e (in-list es)])
                    (define-values (a t) (infer env e))
                    (unify! t 'Int) a))
     (values `(+ ,@anns) 'Int)]

    [`(- ,es ...)
     (define anns (for/list ([e (in-list es)])
                    (define-values (a t) (infer env e))
                    (unify! t 'Int) a))
     (values `(- ,@anns) 'Int)]

    [`(number->string ,e)
     (define-values (a t) (infer env e))
     (unify! t 'Int)
     (values `(number->string ,a) 'String)]

    ;; --- Comparison ---
    [`(= ,a ,b)  (infer-cmp env '= a b)]
    [`(< ,a ,b)  (infer-cmp env '< a b)]
    [`(> ,a ,b)  (infer-cmp env '> a b)]
    [`(<= ,a ,b) (infer-cmp env '<= a b)]
    [`(>= ,a ,b) (infer-cmp env '>= a b)]

    ;; --- Strings ---
    [`(equal? ,es ...)
     (define elem (fresh!))
     (define anns (for/list ([e (in-list es)])
                    (define-values (a t) (infer env e))
                    (unify! t elem) a))
     (values `(equal? ,@anns) 'Bool)]

    [`(string-append ,es ...)
     (define anns (for/list ([e (in-list es)])
                    (define-values (a t) (infer env e))
                    (unify! t 'String) a))
     (values `(string-append ,@anns) 'String)]

    ;; --- Lists ---
    [`(list ,es ...)
     (define elem (fresh!))
     (define anns (for/list ([e (in-list es)])
                    (define-values (a t) (infer env e))
                    (unify! t elem) a))
     (values `(list ,@anns) `(List ,elem))]

    [`(cons ,h ,t)
     (define-values (h* ht) (infer env h))
     (define-values (t* tt) (infer env t))
     (unify! tt `(List ,ht))
     (values `(cons ,h* ,t*) `(List ,ht))]

    [`(car ,e)
     (define-values (a t) (infer env e))
     (define elem (fresh!))
     (unify! t `(List ,elem))
     (values `(car ,a) elem)]

    [`(cdr ,e)
     (define-values (a t) (infer env e))
     (define elem (fresh!))
     (unify! t `(List ,elem))
     (values `(cdr ,a) `(List ,elem))]

    [`(empty? ,e)
     (define-values (a t) (infer env e))
     (define elem (fresh!))
     (unify! t `(List ,elem))
     (values `(empty? ,a) 'Bool)]

    ;; --- Boxes ---
    [`(box ,e)
     (define-values (a t) (infer env e))
     (values `(box ,a) `(Box ,t))]

    [`(unbox ,e)
     (define-values (a t) (infer env e))
     (define elem (fresh!))
     (unify! t `(Box ,elem))
     (values `(unbox ,a) elem)]

    [`(set-box! ,a ,b)
     (define-values (a* at) (infer env a))
     (define-values (b* bt) (infer env b))
     (define elem (fresh!))
     (unify! at `(Box ,elem))
     (unify! bt elem)
     (values `(set-box! ,a* ,b*) elem)]

    ;; --- Structs ---
    [`(struct ,fields ...)
     (define fanns '())
     (define ftypes '())
     (for ([f (in-list fields)])
       (match f
         [`(,name ,val)
          (define-values (a t) (infer env val))
          (set! fanns (append fanns (list (list name a))))
          (set! ftypes (append ftypes (list (list name t))))]))
     (values `(struct ,@fanns) `(Struct ,ftypes))]

    [`(field ,name ,e)
     (define-values (a t) (infer env e))
     (define rt (resolve t))
     (match rt
       [`(Struct ,ftypes)
        (define entry (assq name ftypes))
        (unless entry (error 'type "no field ~a" name))
        (values `(field ,name ,a) (cadr entry))]
       [_ (error 'type "field on non-struct")])]

    ;; --- Exceptions ---
    [`(throw ,e)
     (define-values (a t) (infer env e))
     (unify! t 'String)
     (define result (fresh!))
     (values `(throw ,a) result)]

    [`(catch ,handler ,body)
     (define-values (h* ht) (infer env handler))
     (define-values (b* bt) (infer env body))
     (define result (fresh!))
     (unify! ht `(-> (String) ,result))
     (unify! bt result)
     (values `(catch ,h* ,b*) result)]

    [`(throw-in ,coro ,exn)
     (define-values (c* ct) (infer env coro))
     (define-values (e* et) (infer env exn))
     (unify! et 'String)
     (define result (fresh!))
     (values `(throw-in ,c* ,e*) result)]

    ;; --- Results ---
    [`(ok ,e)
     (define-values (a t) (infer env e))
     (values `(ok ,a) t)]

    [`(err ,e)
     (define-values (a t) (infer env e))
     (unify! t 'String)
     (define result (fresh!))
     (values `(err ,a) result)]

    ;; --- Async ---
    [`(await ,e)
     (define-values (a t) (infer env e))
     (define elem (fresh!))
     (unify! t `(Task ,elem))
     (values `(await ,a) elem)]

    [`(spawn ,e)
     (define-values (a t) (infer env e))
     (values `(spawn ,a) t)]

    [`(cancel ,e)
     (define-values (a t) (infer env e))
     (define elem (fresh!))
     (unify! t `(Task ,elem))
     (values `(cancel ,a) 'Unit)]

    [`(cancelled?)
     (values '(cancelled?) 'Bool)]

    ;; --- Application (MUST BE LAST) ---
    [`(,f ,args ...)
     (define-values (f* ft) (infer env f))
     (define arg-anns '())
     (define arg-ts '())
     (for ([a (in-list args)])
       (define-values (a* at) (infer env a))
       (set! arg-anns (append arg-anns (list a*)))
       (set! arg-ts (append arg-ts (list at))))
     (match (resolve ft)
       [`(async-> ,pts ,ret)
        (unless (= (length pts) (length arg-ts)) (error 'type "arity"))
        (for-each unify! pts arg-ts)
        (values `(,f* ,@arg-anns) `(Task ,ret))]
       [`(-> ,pts ,ret)
        (unless (= (length pts) (length arg-ts)) (error 'type "arity"))
        (for-each unify! pts arg-ts)
        (values `(,f* ,@arg-anns) ret)]
       [_
        (define result (fresh!))
        (unify! ft `(-> ,arg-ts ,result))
        (values `(,f* ,@arg-anns) result)])]

    [_ (error 'type "unhandled: ~a" e)]))

;; Helper for numeric comparison operators
(define (infer-cmp env op a b)
  (define-values (a* at) (infer env a))
  (define-values (b* bt) (infer env b))
  (unify! at 'Int)
  (unify! bt 'Int)
  (values `(,op ,a* ,b*) 'Bool))

;; ---------------------------------------------------------------------------
;; Entry Point
;; ---------------------------------------------------------------------------

(define (type-check e)
  (reset!)
  (with-handlers ([exn:fail? (λ (_) (values #f #f))])
    (define-values (ann type) (infer '() e))
    (values (zonk-expr ann) (zonk type))))

;; ---------------------------------------------------------------------------
;; Tests
;; ---------------------------------------------------------------------------

(module+ test
  (require rackunit)

  (define (tc e)
    (define-values (ann type) (type-check e))
    (and ann (cons ann type)))

  (check-not-false (tc '(+ 1 2)))
  (check-equal? (cdr (tc '(+ 1 2))) 'Int)
  (check-equal? (cdr (tc '(if #t 1 2))) 'Int)
  (check-equal? (cdr (tc '(string-append "a" "b"))) 'String)
  (check-false (tc '(+ 1 "bad")))
  (check-false (tc '(if 1 2 3)))

  (let ([r (tc '(lambda (x) (+ x 1)))])
    (check-not-false r)
    (check-equal? (cdr r) '(-> (Int) Int))
    (check-match (car r) `(typed-lambda (-> (Int) Int) (x) ,_)))

  (let ([r (tc '(async/lambda (x) (+ x 1)))])
    (check-not-false r)
    (check-equal? (cdr r) '(async-> (Int) Int)))

  (let ([r (tc '(let ([x 1]) (+ x 2)))])
    (check-not-false r)
    (check-equal? (cdr r) 'Int))

  (let ([r (tc '(let ([f (lambda (x) (+ x 1))]) (f 41)))])
    (check-not-false r)
    (check-equal? (cdr r) 'Int))

  (check-equal?
   (cdr (tc '(let ([f (async/lambda (x) (+ x 1))]) (await (f 41)))))
   'Int)

  (check-not-false (tc '(box 1)))
  (check-equal? (cdr (tc '(unbox (box 1)))) 'Int)
  (check-equal? (cdr (tc '(car (list 1 2 3)))) 'Int)
  (check-equal? (cdr (tc '(empty? (list)))) 'Bool)

  (check-equal?
   (cdr (tc '(field x (struct [x 1] [y "hello"]))))
   'Int)

  (check-equal?
   (cdr (tc '(catch (lambda (e) 0) (+ 1 2))))
   'Int)

  (let ([r (tc '(letrec ([f (lambda (n) (if (= n 0) 0 (f (- n 1))))]) (f 5)))])
    (check-not-false r)
    (check-equal? (cdr r) 'Int))

  (printf "typecheck tests passed~n"))
