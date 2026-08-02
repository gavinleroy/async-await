#lang racket/base

;; -----------------------------------------------------------------------------
;; C# backend. Input is fully type-annotated; emission is type-directed (no
;; `dynamic`; the only existential is the exception payload). Every function
;; compiles to Func<..., Task<R>>: sync applications await inline, async ones
;; keep the hot Task; `fx` marks async/await only where a body really awaits
;; (else Task.FromResult), so the output compiles warning-free.
;;
;; Semantic mapping (C# is "eager": calling an async function starts it; no
;; spawn/cancel/timeout constructs — a task is just a hot Task<R>):
;;   async/lambda              -> Func<A..., Task<R>> (async lambda; a body
;;                                that never awaits returns Task.FromResult)
;;   (f a...) at async->       -> f(a...)             (hot Task<R>, no await)
;;   (f a...) at ->            -> (await f(a...))     (inline)
;;   (await t), (os/block t)   -> (await t)
;;   (os/io d v)               -> invoked async lambda:
;;                                await Task.Delay(d * 100); return v
;;   throw / catch             -> Err : Exception; try/catch recovering the
;;                                typed payload with a safe `is` pattern
;; -----------------------------------------------------------------------------

(require racket/match
         racket/string
         racket/format
         (only-in racket/list last drop-right))

(provide compile-cs)

(define preamble #<<EOF
using System;
using System.Threading.Tasks;
using System.Collections.Generic;
using System.Linq;

public readonly struct Unit {
    public static readonly Unit U = default;
    public override string ToString() => "()";
}

sealed class Box<T> { public T Value; public Box(T v) { Value = v; } }

sealed class Err : Exception { public readonly object Value; public Err(object v) { Value = v; } }

class Program {
    static Unit Print(string s) { Console.Write(s); return Unit.U; }
    static T Throw<T>(object v) => throw new Err(v);

EOF
)

(define (compile-cs ann)
  (define ty (ann-type ann))
  (string-append
   preamble
   "    static async Task Main() {\n"
   "        try {\n"
   (format "            ~a __result = ~a;\n" (type->cs ty) (emit ann))
   "            Console.Write(__result);\n"
   "        } catch (Exception __ex) {\n"
   "            Console.Write(__ex is Err __e ? __e.Value : (object)__ex);\n"
   "        }\n"
   "    }\n"
   "}\n"))

;; ---------------------------------------------------------------------------
;; Identifiers
;; ---------------------------------------------------------------------------

(define cs-keywords
  '("abstract" "as" "base" "bool" "break" "byte" "case" "catch" "char"
    "checked" "class" "const" "continue" "decimal" "default" "delegate"
    "do" "double" "else" "enum" "event" "explicit" "extern" "false"
    "finally" "fixed" "float" "for" "foreach" "goto" "if" "implicit"
    "in" "int" "interface" "internal" "is" "lock" "long" "namespace"
    "new" "null" "object" "operator" "out" "override" "params" "private"
    "protected" "public" "readonly" "ref" "return" "sbyte" "sealed"
    "short" "sizeof" "stackalloc" "static" "string" "struct" "switch"
    "this" "throw" "true" "try" "typeof" "uint" "ulong" "unchecked"
    "unsafe" "ushort" "using" "virtual" "void" "volatile" "while"
    "async" "await" "dynamic" "var"))

(define (cs-id x)
  (define cleaned (regexp-replace* #rx"[^a-zA-Z0-9_]" (symbol->string x) "_"))
  (if (member cleaned cs-keywords) (string-append "@" cleaned) cleaned))

;; ---------------------------------------------------------------------------
;; Types
;; ---------------------------------------------------------------------------

(define (type->cs t)
  (match t
    ['Int "int"]
    ['String "string"]
    ['Bool "bool"]
    ['Unit "Unit"]
    [`(-> ,args ,ret)      (func-type args ret)]
    [`(async-> ,args ,ret) (func-type args ret)]
    [`(Task ,t) (format "Task<~a>" (type->cs t))]
    [`(List ,t) (format "List<~a>" (type->cs t))]
    [`(Box ,t) (format "Box<~a>" (type->cs t))]
    [_ (error 'compile-cs "no C# type for: ~s" t)]))

;; All functions are async: Func<A..., Task<R>>  (Func<Task<R>> for 0 args)
(define (func-type args ret)
  (format "Func<~a>"
          (string-join (append (map type->cs args) (list (format "Task<~a>" (type->cs ret))))
                       ", ")))

(define (default-cs t)
  (format "default(~a)" (type->cs t)))

;; ---------------------------------------------------------------------------
;; Annotation helpers
;; ---------------------------------------------------------------------------

(define (ann-type a)
  (match a
    [`(: ,_ ,ty) ty]
    [`(typed-lambda ,ft ,_ ,_) ft]
    [`(typed-async-lambda ,ft ,_ ,_) ft]
    [_ (error 'compile-cs "unannotated node: ~s" a)]))

(define (lambda-rhs? rhs)
  (match rhs
    [(or `(typed-lambda ,_ ,_ ,_) `(typed-async-lambda ,_ ,_ ,_)) #t]
    [_ #f]))

;; ---------------------------------------------------------------------------
;; Effects: does a node await? (does not cross lambda or task-creation bodies)
;; Used to mark lambdas/IIFEs `async` only when they actually await (else C#
;; warns CS1998), and to place `await` at the awaiting site.
;; ---------------------------------------------------------------------------

(define (fx a)
  (match a
    [(or `(typed-lambda ,_ ,_ ,_) `(typed-async-lambda ,_ ,_ ,_)) #f]
    [`(: ,form ,ty) (fx-form form ty)]
    [_ (error 'compile-cs "unannotated node: ~s" a)]))

(define (fx-any . as) (ormap fx as))
(define (fx-any* as) (ormap fx as))

(define (fx-form form ty)
  (match form
    [(? number?) #f] [(? string?) #f] [(? boolean?) #f] [(? symbol?) #f]
    [`(void) #f] [`(ptr ,_) #f] [`(os/time) #f]
    [`(os/io ,_ ,_) #f]                    ; invoking the async lambda is not an await
    [(or `(await ,_) `(os/block ,_)) #t]
    [`(throw ,_) #f]
    [`(throw-in ,_ ,_) #f]
    [`(err ,_) #f]
    [`(catch ,_ ,_) #t]
    [`(ok ,e) (fx e)]
    [`(if ,c ,t ,f) (fx-any c t f)]
    [`(when ,c ,es ...) (fx-any* (cons c es))]
    [`(begin ,es ...) (fx-any* es)]
    [`(set! ,_ ,rhs) (fx rhs)]
    [`(let (,cs ...) ,body) (or (ormap (lambda (c) (fx (cadr c))) cs) (fx body))]
    [`(let* (,cs ...) ,body) (or (ormap (lambda (c) (fx (cadr c))) cs) (fx body))]
    [`(letrec (,cs ...) ,body)
     (or (fx body)
         (ormap (lambda (c) (if (lambda-rhs? (cadr c)) #f (fx (cadr c)))) cs))]
    [(or `(+ ,es ...) `(- ,es ...) `(list ,es ...) `(equal? ,es ...)
         `(string-append ,es ...))
     (fx-any* es)]
    [(or `(= ,a ,b) `(< ,a ,b) `(> ,a ,b) `(<= ,a ,b) `(>= ,a ,b) `(cons ,a ,b)
         `(set-box! ,a ,b))
     (fx-any a b)]
    [(or `(number->string ,e) `(car ,e) `(cdr ,e) `(empty? ,e)
         `(box ,e) `(unbox ,e) `(print ,e) `(field ,_ ,e))
     (fx e)]
    [`(,f ,args ...)
     (match (ann-type f)
       [`(async-> ,_ ,_) (fx-any* args)]   ; hot Task, no await here
       [`(-> ,_ ,_) #t])]                  ; awaited inline
    [_ (error 'compile-cs "fx: unsupported form: ~s" form)]))

;; ---------------------------------------------------------------------------
;; Emit (self-contained: each result carries its own `await`)
;; ---------------------------------------------------------------------------

(define (emit a)
  (match a
    [(or `(typed-lambda ,ft ,xs ,body) `(typed-async-lambda ,ft ,xs ,body))
     (emit-fn ft xs body)]
    [`(: ,form ,ty) (emit-form form ty)]
    [_ (error 'compile-cs "unannotated node: ~s" a)]))

;; A function value: Func<A..., Task<R>>. Async only if its body awaits;
;; otherwise it returns a completed Task so callers can still await it.
(define (emit-fn ft xs body)
  (match-define (or `(-> ,atys ,rty) `(async-> ,atys ,rty)) ft)
  (define ftc (func-type atys rty))
  (define rc (type->cs rty))
  (define params
    (string-join (map (lambda (x t) (format "~a ~a" (type->cs t) (cs-id x))) xs atys) ", "))
  (if (fx body)
      (format "((~a)(async (~a) => { return ~a; }))" ftc params (emit body))
      (format "((~a)((~a) => { return Task.FromResult<~a>(~a); }))" ftc params rc (emit body))))

(define (emit-form form ty)
  (match form
    ;; --- Literals / atoms ---
    [(? number? n) (~a n)]
    [(? string? s) (~v s)]
    [#true "true"]
    [#false "false"]
    [`(void) "Unit.U"]
    [(? symbol? x) (cs-id x)]
    [`(ptr ,x) (cs-id x)]

    ;; --- Binding ---
    [`(let (,cs ...) ,body)  (emit-let cs body ty)]
    [`(let* (,cs ...) ,body) (emit-let cs body ty)]   ; sequential locals (see note)
    [`(letrec (,cs ...) ,body) (emit-letrec cs body ty)]

    ;; --- Sequencing / control ---
    [`(begin ,es ...) (emit-begin es ty)]
    [`(if ,c ,t ,f)
     (iife ty (fx-any c t f)
           (format "if (~a) { return ~a; } else { return ~a; }" (emit c) (emit t) (emit f)))]
    [`(when ,c ,es ...)
     (iife ty (fx-any* (cons c es))
           (format "if (~a) { ~a } return Unit.U;"
                   (emit c)
                   (string-join (for/list ([e (in-list es)]) (format "_ = ~a;" (emit e))) " ")))]
    [`(set! ,x ,rhs)
     (iife ty (fx rhs) (format "~a = ~a; return ~a;" (cs-id x) (emit rhs) (cs-id x)))]

    ;; --- Print ---
    [`(print ,e) (format "Print(~a)" (emit e))]

    ;; --- Async ---
    [(or `(await ,t) `(os/block ,t)) (format "(await ~a)" (emit t))]
    [`(os/io ,d ,v)
     (match-define `(Task ,vt) ty)
     (format "((Func<Task<~a>>)(async () => { await Task.Delay(~a * 100); return ~a; }))()"
             (type->cs vt) (emit d) (emit v))]
    [`(os/time) "(int)DateTimeOffset.UtcNow.ToUnixTimeMilliseconds()"]

    ;; --- Exceptions ---
    [`(throw ,e)      (format "Throw<~a>(~a)" (type->cs ty) (emit e))]
    [`(throw-in ,_ ,e) (format "Throw<~a>(~a)" (type->cs ty) (emit e))]
    [`(catch ,handler ,body) (emit-catch handler body ty)]

    ;; --- Results ---
    [`(ok ,e) (emit e)]
    [`(err ,e) (format "Throw<~a>(~a)" (type->cs ty) (emit e))]

    ;; --- Arithmetic / comparison / strings ---
    [`(+ ,es ...) (emit-binop "+" es "0")]
    [`(- ,es ...)
     (match es ['() "0"] [(list a) (format "(-~a)" (emit a))]
       [_ (format "(~a)" (string-join (map emit es) " - "))])]
    [`(= ,a ,b)  (format "(~a == ~a)" (emit a) (emit b))]
    [`(< ,a ,b)  (format "(~a < ~a)"  (emit a) (emit b))]
    [`(> ,a ,b)  (format "(~a > ~a)"  (emit a) (emit b))]
    [`(<= ,a ,b) (format "(~a <= ~a)" (emit a) (emit b))]
    [`(>= ,a ,b) (format "(~a >= ~a)" (emit a) (emit b))]
    [`(number->string ,e) (format "(~a).ToString()" (emit e))]
    [`(equal? ,es ...)
     (match es [(or '() (list _)) "true"]
       [(list a b _ ...) (format "(~a == ~a)" (emit a) (emit b))])]
    [`(string-append ,es ...)
     (match es ['() "\"\""] [_ (format "(~a)" (string-join (map emit es) " + "))])]

    ;; --- Lists / boxes ---
    [`(list ,es ...)
     (match-define `(List ,et) ty)
     (format "new List<~a> { ~a }" (type->cs et) (string-join (map emit es) ", "))]
    [`(cons ,h ,t)
     (match-define `(List ,et) ty)
     (format "new List<~a> { ~a }.Concat(~a).ToList()" (type->cs et) (emit h) (emit t))]
    [`(car ,e) (format "(~a)[0]" (emit e))]
    [`(cdr ,e) (format "(~a).GetRange(1, (~a).Count - 1)" (emit e) (emit e))]
    [`(empty? ,e) (format "((~a).Count == 0)" (emit e))]
    [`(box ,e)
     (match-define `(Box ,et) ty)
     (format "new Box<~a>(~a)" (type->cs et) (emit e))]
    [`(unbox ,e) (format "(~a).Value" (emit e))]
    [`(set-box! ,a ,b)
     (iife ty (fx-any a b)
           (format "(~a).Value = ~a; return (~a).Value;" (emit a) (emit b) (emit a)))]

    ;; --- Application (must be last) ---
    [`(,f ,args ...) (emit-app f args ty)]

    [_ (error 'compile-cs "unsupported form: ~s" form)]))

(define (emit-binop op es identity)
  (match es ['() identity] [(list a) (emit a)]
    [_ (format "(~a)" (string-join (map emit es) (format " ~a " op)))]))

;; An immediately-invoked lambda: async (awaited) when its body awaits, else a
;; plain lambda returning the value directly.
(define (iife ty awaits? stmts)
  (if awaits?
      (format "(await ((Func<Task<~a>>)(async () => { ~a }))())" (type->cs ty) stmts)
      (format "((Func<~a>)(() => { ~a }))()" (type->cs ty) stmts)))

;; `let`/`let*` compile to a sequence of typed C# locals. A type-checked `let`
;; never has a clause referring to a sibling (rhss are typed in the outer
;; scope), so sequential locals preserve its meaning. C# locals are mutable,
;; so `set!` on a let-binding works.
(define (emit-let cs body ty)
  (define aw (or (ormap (lambda (c) (fx (cadr c))) cs) (fx body)))
  (define binds
    (string-join
     (for/list ([c (in-list cs)])
       (match-define (list x rhs) c)
       (format "~a ~a = ~a;" (type->cs (ann-type rhs)) (cs-id x) (emit rhs)))
     " "))
  (iife ty aw (format "~a return ~a;" binds (emit body))))

;; `letrec` binds (possibly mutually recursive) functions; emit them as C#
;; local functions, which may reference themselves and each other.
(define (emit-letrec cs body ty)
  (define aw
    (or (fx body)
        (ormap (lambda (c) (if (lambda-rhs? (cadr c)) #f (fx (cadr c)))) cs)))
  (define decls
    (string-join
     (for/list ([c (in-list cs)])
       (match-define (list x rhs) c)
       (match rhs
         [(or `(typed-lambda (-> ,atys ,rty) ,xs ,b)
              `(typed-async-lambda (async-> ,atys ,rty) ,xs ,b))
          (define rc (type->cs rty))
          (define params
            (string-join (map (lambda (p t) (format "~a ~a" (type->cs t) (cs-id p))) xs atys) ", "))
          (if (fx b)
              (format "async Task<~a> ~a(~a) { return ~a; }" rc (cs-id x) params (emit b))
              (format "Task<~a> ~a(~a) { return Task.FromResult<~a>(~a); }" rc (cs-id x) params rc (emit b)))]
         [_ (format "~a ~a = ~a;" (type->cs (ann-type rhs)) (cs-id x) (emit rhs))]))
     " "))
  (iife ty aw (format "~a return ~a;" decls (emit body))))

(define (emit-begin es ty)
  (match es
    ['() "Unit.U"]
    [(list e) (emit e)]
    [_
     (define inits
       (string-join (for/list ([e (in-list (drop-right es 1))]) (format "_ = ~a;" (emit e))) " "))
     (iife ty (fx-any* es) (format "~a return ~a;" inits (emit (last es))))]))

;; catch : Tb. handler : (Th) -> Tr (Tr coincides with Tb in well-formed
;; programs). An explicit throw carries a typed payload recovered with a safe
;; `is` pattern; cancellation/other errors give the handler a default Th — our
;; handlers either ignore the argument or the thrown type already matches.
(define (emit-catch handler body ty)
  (match-define (or `(typed-lambda (-> (,th) ,tr) ,_ ,_)
                    `(typed-async-lambda (async-> (,th) ,tr) ,_ ,_)) handler)
  (define tbc (type->cs ty))
  (define thc (type->cs th))
  (define hft (func-type (list th) tr))
  (format
   (string-append
    "(await ((Func<Task<~a>>)(async () => { "
    "~a __h = ~a; "
    "try { return ~a; } "
    "catch (Err __e) { return await __h(__e.Value is ~a __v ? __v : ~a); } "
    "catch { return await __h(~a); } }))())")
   tbc hft (emit handler) (emit body) thc (default-cs th) (default-cs th)))

(define (emit-app f args ty)
  (define fcode (emit f))
  (define argcode (string-join (map emit args) ", "))
  (match (ann-type f)
    [`(async-> ,_ ,_) (format "~a(~a)" fcode argcode)]          ; hot Task<R>
    [`(-> ,_ ,_) (format "(await ~a(~a))" fcode argcode)]))     ; await -> R
