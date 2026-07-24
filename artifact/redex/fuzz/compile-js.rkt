#lang racket/base

(require racket/match
         racket/string
         racket/format
         (only-in racket/list last drop-right take))

(provide compile-js compile-ts)

(define preamble #<<EOF
function __cons(h, t) { return [h, ...t]; }
function __car(l) { return l[0]; }
function __cdr(l) { return l.slice(1); }
function __isEmpty(l) { return l.length === 0; }
function __box(v) { return { value: v }; }
function __unbox(b) { return b.value; }
function __setBox(b, v) { return (b.value = v); }
function __print(s) { process.stdout.write(String(s)); }
EOF
)

(define (compile-js e)
  (string-append
   preamble "\n\n"
   "(async () => {\n"
   "  return " (emit e) ";\n"
   "})().then(v => console.log(v)).catch(e => { console.error(e); process.exit(1); });\n"))

(define (compile-ts e) (compile-js e))

;; ---------------------------------------------------------------------------
;; Type rendering (TypeScript)
;; ---------------------------------------------------------------------------

(define (type->ts t)
  (match t
    ['Int "number"]
    ['String "string"]
    ['Bool "boolean"]
    ['Unit "void"]
    [`(-> ,args ,ret)
     (define params
       (string-join (for/list ([a (in-list args)] [i (in-naturals)])
                      (format "a~a: ~a" i (type->ts a))) ", "))
     (format "((~a) => ~a)" params (type->ts ret))]
    [`(async-> ,args ,ret)
     (define params
       (string-join (for/list ([a (in-list args)] [i (in-naturals)])
                      (format "a~a: ~a" i (type->ts a))) ", "))
     (format "((~a) => Promise<~a>)" params (type->ts ret))]
    [`(List ,t) (format "~a[]" (type->ts-atom t))]
    [`(Box ,t) (format "{ value: ~a }" (type->ts t))]
    [`(Task ,t) (format "Promise<~a>" (type->ts t))]
    [`(Struct ,fields)
     (format "{ ~a }"
             (string-join (map (λ (f) (format "~a: ~a" (sanitize-var (car f)) (type->ts (cadr f))))
                               fields) ", "))]
    [_ "any"]))

(define (type->ts-atom t)
  (match t
    [(or 'Int 'String 'Bool 'Unit) (type->ts t)]
    [_ (format "(~a)" (type->ts t))]))

(define (sanitize-var x)
  (define s (symbol->string x))
  (regexp-replace* #rx"[^a-zA-Z0-9_$]" s "_"))

(define (emit e)
  (match e
    ;; --- Literals ---
    [(? number? n) (~a n)]
    [(? string? s) (~v s)]
    [#true "true"]
    [#false "false"]
    [(? symbol? x) (sanitize-var x)]

    ;; --- Core forms ---
    [`(void) "undefined"]
    [`(ptr ,x) (sanitize-var x)]

    [`(: ,inner ,_) (emit inner)]

    ;; Type annotations are dropped: the output runs under plain node.
    [`(typed-lambda ,_ ,xs ,body)
     (emit `(lambda ,xs ,body))]

    [`(typed-async-lambda ,_ ,xs ,body)
     (emit `(async/lambda ,xs ,body))]

    [`(lambda (,xs ...) ,body)
     (format "(function(~a) { return ~a; })"
             (string-join (map sanitize-var xs) ", ")
             (emit body))]

    [`(async/lambda (,xs ...) ,body)
     (format "(async function(~a) { return ~a; })"
             (string-join (map sanitize-var xs) ", ")
             (emit body))]

    ;; Binding/sequencing forms use async IIFEs: their bodies may contain
    ;; `await`, which is illegal inside a synchronous arrow.
    [`(letrec (,clauses ...) ,body)
     (define decls
       (for/list ([c (in-list clauses)])
         (match c
           [`(,x ,rhs) (format "let ~a = ~a;" (sanitize-var x) (emit rhs))]
           [_ ""])))
     (format "(await (async () => { ~a return ~a; })())"
             (string-join decls " ")
             (emit body))]

    ;; --- Binding ---
    [`(let (,clauses ...) ,body)
     (define decls
       (for/list ([c (in-list clauses)])
         (match c
           [`(,x ,rhs) (format "let ~a = ~a;" (sanitize-var x) (emit rhs))]
           [_ ""])))
     (format "(await (async () => { ~a return ~a; })())"
             (string-join decls " ")
             (emit body))]

    ;; let declarations are evaluated in order, so let* = let
    [`(let* (,clauses ...) ,body)
     (emit `(let ,clauses ,body))]

    ;; --- When ---
    [`(when ,c ,es ...)
     (emit `(if ,c (begin ,@es (void)) (void)))]

    ;; --- Print (no newline) ---
    [`(print ,e)
     (format "__print(~a)" (emit e))]

    ;; --- Control flow ---
    [`(if ,c ,t ,f)
     (format "(~a ? ~a : ~a)" (emit c) (emit t) (emit f))]

    [`(begin ,es ...)
     (match es
       ['() "undefined"]
       [(list e) (emit e)]
       [_
        (define stmts (map emit (drop-right es 1)))
        (define last-e (emit (last es)))
        (format "(await (async () => { ~a return ~a; })())"
                (string-join (map (lambda (s) (string-append s ";")) stmts) " ")
                last-e)])]

    [`(set! ,x ,rhs)
     (format "(~a = ~a)" (sanitize-var x) (emit rhs))]

    ;; --- Async ---
    [`(await ,e)
     (format "(await ~a)" (emit e))]

    [`(os/block ,e)
     (format "(await ~a)" (emit e))]

    ;; Model delays are logical units ordered by deadline, not durations.
    ;; 20ms per unit (matching the python backends) keeps that ordering
    ;; robust: raw-millisecond deadlines 1 apart can invert under node's ~1ms
    ;; timer wheel (probed: a 2ms timer fired between two 1ms timers).
    [`(os/io ,delay ,val)
     (format "(await new Promise(r => setTimeout(() => r(~a), (~a) * 20)))"
             (emit val) (emit delay))]

    [`(os/time)
     "Date.now()"]

    [`(os/start-soon ,e)
     (format "setTimeout(() => ~a, 0)" (emit e))]

    [`(os/start-later ,time ,_label ,e)
     (format "setTimeout(() => ~a, ~a)" (emit e) (emit time))]

    ;; --- Exceptions ---
    [`(throw ,e)
     (format "(() => { throw ~a; })()" (emit e))]

    [`(catch ,handler ,body)
     (format "(await (async () => { try { return ~a; } catch(__e) { return (~a)(__e); } })())"
             (emit body) (emit handler))]

    [`(throw-in ,coro ,exn)
     (format "(() => { throw ~a; })()" (emit exn))]

    ;; --- Results ---
    [`(ok ,e) (emit e)]
    [`(err ,e) (format "(() => { throw ~a; })()" (emit e))]

    ;; --- Arithmetic ---
    [`(+ ,es ...)
     (match es
       ['() "0"]
       [(list a) (emit a)]
       [_ (format "(~a)" (string-join (map emit es) " + "))])]

    [`(- ,es ...)
     (match es
       ['() "0"]
       [(list a) (format "(-~a)" (emit a))]
       [_ (format "(~a)" (string-join (map emit es) " - "))])]

    [`(number->string ,e)
     (format "String(~a)" (emit e))]

    ;; --- Comparison ---
    [`(= ,a ,b) (format "(~a === ~a)" (emit a) (emit b))]
    [`(< ,a ,b) (format "(~a < ~a)" (emit a) (emit b))]
    [`(> ,a ,b) (format "(~a > ~a)" (emit a) (emit b))]
    [`(<= ,a ,b) (format "(~a <= ~a)" (emit a) (emit b))]
    [`(>= ,a ,b) (format "(~a >= ~a)" (emit a) (emit b))]

    ;; --- Strings ---
    [`(equal? ,es ...)
     (match es
       ['() "true"]
       [(list _) "true"]
       [(list a b) (format "(~a === ~a)" (emit a) (emit b))]
       [(list a b rest ...) (format "(~a === ~a)" (emit a) (emit b))])]

    [`(string-append ,es ...)
     (match es
       ['() "\"\""]
       [_ (format "(~a)" (string-join (map (lambda (x) (format "String(~a)" (emit x))) es) " + "))])]

    ;; --- Lists ---
    [`(list ,es ...)
     (format "[~a]" (string-join (map emit es) ", "))]

    [`(cons ,h ,t)
     (format "__cons(~a, ~a)" (emit h) (emit t))]

    [`(car ,e)
     (format "__car(~a)" (emit e))]

    [`(cdr ,e)
     (format "__cdr(~a)" (emit e))]

    [`(empty? ,e)
     (format "__isEmpty(~a)" (emit e))]

    ;; --- Boxes (mutable refs) ---
    [`(box ,e)
     (format "__box(~a)" (emit e))]

    [`(unbox ,e)
     (format "__unbox(~a)" (emit e))]

    [`(set-box! ,a ,b)
     (format "__setBox(~a, ~a)" (emit a) (emit b))]

    ;; --- Structs ---
    [`(struct ,fields ...)
     (define pairs
       (for/list ([f (in-list fields)])
         (match f
           [`(,name ,val) (format "~a: ~a" (sanitize-var name) (emit val))]
           [_ ""])))
     (format "({ ~a })" (string-join pairs ", "))]

    [`(field ,name ,e)
     (format "~a.~a" (emit e) (sanitize-var name))]

    ;; --- Application (must be last to avoid matching other forms) ---
    [`(,f ,args ...)
     (format "(~a)(~a)" (emit f) (string-join (map emit args) ", "))]

    [_ (format "/* unhandled: ~s */ undefined" e)]))

