#lang racket/base

;; -----------------------------------------------------------------------------
;; Type-directed generator for async programs.
;;
;; Produces closed, well-typed programs in the models' shared surface syntax,
;; dense in the constructs under test: async/lambda, await, spawn, cancel,
;; os/io delays, and printed traces. Programs use only true grammar forms
;; (nested single-clause `let`, `begin`, `if`, boxes, string-append, ...) so
;; the SAME term runs in the redex model and compiles to every runtime.
;;
;; Observability: programs write traces with `(print ...)` and end with
;; `(print "|<value>")`, evaluating to "". To the typechecker and the
;; compilers `(print e)` is a built-in form writing to stdout; in the model
;; the same s-expression is an application of the `print` lambda bound by
;; wrapping the program in the trace-stdout expansion (see wrap-for-model in
;; main.rkt). Either way the observable is the string "<trace>|<value>".
;;
;; Per-language typing of async calls:
;;   lazy  (asyncio trio tokio smol): call yields a *coroutine*; `spawn`
;;         turns it into a task; `await` accepts either.
;;   eager (javascript csharp swift): call yields a running task-like;
;;         there is no `spawn` (and JS/C# have no `cancel`).
;; Generated async functions only ever return base types, which also
;; satisfies Swift's no-task-typed-results restriction.
;;
;; Every generated program is re-validated with the real type-check; any
;; disagreement raises exn:fail (generator drift = loud crash).
;; -----------------------------------------------------------------------------

(require racket/match
         racket/list
         racket/string
         "../typecheck.rkt")

(provide generate-program
         (struct-out gen-program)
         typegen-languages)

;; ---------------------------------------------------------------------------
;; Per-language capabilities
;; ---------------------------------------------------------------------------

;; family       : 'lazy (call → coroutine) | 'eager (call → task)
;; spawn?       : (spawn coro) available
;; cancel       : #f | 'catch  (cancel, then await under catch     — aio/trio/swift)
;;              |      'leak   (cancel as statement, never awaited — tokio)
;;              |      'await  ((await (cancel t)) idiom           — smol)
(struct lang-info (family spawn? cancel) #:transparent)

(define language-table
  (hasheq 'asyncio    (lang-info 'lazy  #t 'catch)
          'trio       (lang-info 'lazy  #t 'catch)
          'tokio      (lang-info 'lazy  #t 'leak)
          'smol       (lang-info 'lazy  #t 'await)
          'javascript (lang-info 'eager #f #f)
          'csharp     (lang-info 'eager #f #f)
          'swift      (lang-info 'eager #f 'catch)))

(define typegen-languages (hash-keys language-table))

;; The Rust runtimes (and only they) model JoinHandle::await as a Result:
;; awaiting a spawned task yields a struct {type, value}, so the generator
;; unwraps the `value` field wherever it consumes a handle's result.
(define (rust-lang? lang) (and (memq lang '(tokio smol)) #t))

;; ---------------------------------------------------------------------------
;; Generation state
;; ---------------------------------------------------------------------------

;; term      : the surface program (model syntax, runs in redex)
;; annotated : the type-annotated form (input to the compile-* backends)
(struct gen-program (lang term annotated) #:transparent)

(define current-rng (make-parameter (current-pseudo-random-generator)))

(define (rand n) (random n (current-rng)))
(define (pick lst) (list-ref lst (rand (length lst))))
(define (chance p) (< (random (current-rng)) p))

(define fresh-counter (make-parameter #f))
(define (fresh! prefix)
  (define n (fresh-counter))
  (hash-update! n prefix add1 0)
  (string->symbol (format "~a~a" prefix (hash-ref n prefix))))

;; Trace letters are unique per program so any interleaving is recoverable
;; from the final string.
(define trace-letters (make-parameter #f))
(define (next-trace-letter!)
  (define b (trace-letters))
  (define letter (string (integer->char (+ (char->integer #\A) (unbox b)))))
  (set-box! b (add1 (unbox b)))
  letter)

;; A small delay keeps model reduction sequences short.
(define (small-delay) (add1 (rand 4)))

;; ---------------------------------------------------------------------------
;; Term builders (all true grammar forms)
;; ---------------------------------------------------------------------------

;; trace write in statement position
(define (trace-stmt)
  `(print ,(next-trace-letter!)))

;; Sequential scoping needs nested single-clause lets: the model's `let`
;; binds in the body only.
(define (let1* bindings body)
  (for/foldr ([acc body]) ([b (in-list bindings)])
    `(let (,b) ,acc)))

(define (render-value e τ)
  (match τ
    ['String e]
    ['Int `(number->string ,e)]))

;; ---------------------------------------------------------------------------
;; Expression generation (values of base type)
;; ---------------------------------------------------------------------------

;; Γ maps variable -> type; used to reuse in-scope values.
(define (gen-base-expr Γ τ fuel)
  (define vars (for/list ([(x t) (in-hash Γ)] #:when (equal? t τ)) x))
  (cond
    [(and (pair? vars) (chance 0.5)) (pick vars)]
    [(zero? fuel) (canonical τ)]
    [else
     (match τ
       ['Int
        (pick (list (rand 100)
                    `(+ ,(gen-base-expr Γ 'Int (sub1 fuel))
                        ,(gen-base-expr Γ 'Int (sub1 fuel)))))]
       ['String
        (pick (list (format "s~a" (rand 10))
                    `(string-append ,(gen-base-expr Γ 'String (sub1 fuel))
                                    ,(gen-base-expr Γ 'String (sub1 fuel)))))])]))

(define (canonical τ)
  (match τ
    ['Int 0]
    ['String "s"]))

(define (base-type) (pick '(Int String)))

;; ---------------------------------------------------------------------------
;; Helper (worker) functions
;; ---------------------------------------------------------------------------

;; A helper: (async/lambda (params ...) body) returning a base type.
;; Bodies interleave os/io suspensions, trace writes, and possibly awaiting
;; an earlier helper (call graph is a DAG: helper i only calls j < i, so
;; programs terminate without recursion).
(struct helper (name params ret) #:transparent)

(define (gen-helper info earlier)
  (define name (fresh! 'work))
  (define nparams (rand 2))
  (define params
    (for/list ([_ (in-range nparams)])
      (cons (fresh! 'msg) 'String)))
  (define ret (base-type))
  (define Γ (for/fold ([h (hash)]) ([p (in-list params)])
              (hash-set h (car p) (cdr p))))
  (define stmts
    (filter values
            (list (trace-stmt)
                  `(await (os/io ,(small-delay) (void)))
                  (and (pair? earlier) (chance 0.5)
                       (let ([h (pick earlier)])
                         ;; await a sub-helper; lazy: awaits the coroutine
                         ;; inline, eager: awaits the started task
                         `(await (,(helper-name h)
                                  ,@(map (lambda (_) (gen-base-expr Γ 'String 1))
                                         (helper-params h))))))
                  (and (chance 0.6) (trace-stmt)))))
  (define result
    (if (and (eq? ret 'String) nparams (pair? params) (chance 0.5))
        (car (pick params))
        (gen-base-expr Γ ret 1)))
  (values (helper name params ret)
          `(async/lambda ,(map car params)
                         (begin ,@stmts ,result))))

;; ---------------------------------------------------------------------------
;; Main orchestration body
;; ---------------------------------------------------------------------------

;; Create 1-3 tasks from the helpers, interleave traces and delays, cancel
;; some (per the language's idiom), and await the rest. Every task is
;; consumed: awaited, or cancelled via the language's safe pattern.
(define (gen-main info helpers rust?)
  (define (call-helper h)
    `(,(helper-name h)
      ,@(map (lambda (_) (gen-base-expr (hash) 'String 1)) (helper-params h))))

  ;; the expression that makes a Task from helper h
  (define (make-task h)
    (match (lang-info-family info)
      ['lazy `(spawn ,(call-helper h))]
      ['eager (call-helper h)]))

  (define ntasks (add1 (rand 3)))
  (define tasks
    (for/list ([_ (in-range ntasks)])
      (define h (pick helpers))
      (list (fresh! 't) h)))

  ;; Per-task consumption plan
  (define cancel-style (lang-info-cancel info))
  (define plans
    (for/list ([t (in-list tasks)])
      (if (and cancel-style (chance 0.35))
          (list (car t) (cadr t) 'cancel)
          (list (car t) (cadr t) 'await))))

  ;; Build: bind all tasks first (so they run concurrently), then a body of
  ;; interleaved traces/delays/awaits. The main's value is the last awaited
  ;; task's value (rendered), or a literal when everything is cancelled.
  (define bindings (for/list ([t (in-list tasks)])
                     `[,(car t) ,(make-task (cadr t))]))

  (define mid-stmts
    (filter values
            (list (trace-stmt)
                  (and (chance 0.5) `(await (os/io ,(small-delay) (void)))))))

  (define consume-stmts
    (for/list ([p (in-list plans)])
      (match-define (list tname h how) p)
      (match how
        ['await `(await ,tname)]
        ['cancel
         (match cancel-style
           ;; cancel then await under catch: the await may raise the
           ;; cancellation, which the handler converts to a marker string
           ['catch `(begin (cancel ,tname)
                           (catch (lambda (e) ,(trace-stmt))
                                  (begin (await ,tname) (void))))]
           ;; tokio: abort and walk away; the runtime drains it
           ['leak `(cancel ,tname)]
           ;; smol: cancelling is itself awaitable
           ['await `(await (cancel ,tname))])])))

  ;; main returns a base-typed value. The awaited task is a spawned handle
  ;; (lazy runtimes) or a started task (eager); for Rust the handle awaits to a
  ;; Result struct, so unwrap its `value` field to recover the base value.
  (define awaited (for/first ([p (in-list plans)] #:when (eq? (caddr p) 'await)) p))
  (define-values (result rtype)
    (if awaited
        (values (let ([aw `(await ,(car awaited))])
                  (if rust? `(field value ,aw) aw))
                (helper-ret (cadr awaited)))
        (values (gen-base-expr (hash) 'String 1) 'String)))

  ;; consume-stmts for awaited tasks yield their value; re-awaiting for the
  ;; result is not allowed (tasks are consumed once), so when the result
  ;; re-uses a task we drop its consume statement.
  (define stmts
    (append mid-stmts
            (for/list ([p (in-list plans)]
                       #:unless (and awaited (eq? (car p) (car awaited))
                                     (eq? (caddr p) 'await)))
              (for/first ([s (in-list consume-stmts)]
                          [q (in-list plans)]
                          #:when (eq? (car q) (car p)))
                s))))

  (values
   `(async/lambda ()
      ,(let1* bindings
              (if (null? stmts)
                  result
                  `(begin ,@stmts ,result))))
   rtype))

;; ---------------------------------------------------------------------------
;; Whole programs
;; ---------------------------------------------------------------------------

;; (let ([work1 (async/lambda ...)]) ...
;;   (let ([main (async/lambda () ...)])
;;     (let ([v (os/block (main))])
;;       (begin (print (string-append "|" (render v))) ""))))
(define (generate-program lang
                          #:helpers [nhelpers #f]
                          #:seed [seed #f])
  (define info (hash-ref language-table lang
                         (lambda () (error 'typegen "unknown language: ~a" lang))))
  (define rust? (rust-lang? lang))
  (parameterize ([current-rng (if seed
                                  (let ([g (make-pseudo-random-generator)])
                                    (parameterize ([current-pseudo-random-generator g])
                                      (random-seed seed))
                                    g)
                                  (current-rng))]
                 [fresh-counter (make-hasheq)]
                 [trace-letters (box 0)])
    ;; the helper-count draw must happen INSIDE the seeded region: as a
    ;; default-argument expression it drew from the ambient generator
    ;; before the parameterize, so `#:seed` never fully pinned the program
    (define nh (or nhelpers (add1 (rand 2))))
    (define-values (helpers helper-terms)
      (for/fold ([hs '()] [terms '()] #:result (values (reverse hs) (reverse terms)))
                ([_ (in-range nh)])
        (define-values (h term) (gen-helper info hs))
        (values (cons h hs) (cons term terms))))

    (define-values (main-term _rtype) (gen-main info helpers rust?))

    (define root-call
      ;; lazy: (main) is a coroutine, os/block drives it
      ;; eager: (main) is already a task
      `(os/block (main)))

    (define rtype _rtype)
    (define term
      (let1* (append (for/list ([h (in-list helpers)] [t (in-list helper-terms)])
                       `[,(helper-name h) ,t])
                     `([main ,main-term]))
             `(let ([v ,root-call])
                (begin (print (string-append "|" ,(render-value 'v rtype)))
                       ""))))

    ;; Safety net: the real typechecker must agree, and the program must be
    ;; a String producer.
    (define-values (ann τ) (type-check term #:rust? rust?))
    (unless ann
      (error 'typegen "generated ill-typed term (drift!): ~s" term))
    (unless (equal? τ 'String)
      (error 'typegen "root type ~s, expected String: ~s" τ term))
    (gen-program lang term ann)))

;; ---------------------------------------------------------------------------
;; Tests
;; ---------------------------------------------------------------------------

(module+ test
  (require rackunit)

  (for ([lang (in-list typegen-languages)])
    (for ([i (in-range 200)])
      (define p (generate-program lang))
      ;; generate-program already asserts type-correctness; check shape
      (check-pred pair? (gen-program-term p))
      ;; no disallowed forms outside the whitelisted catch-handler position
      (let loop ([t (gen-program-term p)] [in-catch-handler? #f])
        (when (pair? t)
          (match t
            [`(catch (lambda (,_) ,handler-body) ,body)
             (loop handler-body #t)
             (loop body #f)]
            [`(lambda ,_ ,_)
             (check-true in-catch-handler?
                         (format "bare lambda outside catch handler: ~s" t))]
            [_ (for ([s (in-list t)]) (loop s in-catch-handler?))])))))

  (printf "typegen: 200 programs x ~a languages generated and validated~n"
          (length typegen-languages)))
