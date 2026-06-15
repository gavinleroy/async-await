#lang racket/base

;; -----------------------------------------------------------------------------
;; Swift backend.
;;
;; Input is a fully type-annotated program (every node is `(: e τ)`, lambdas
;; carry their function type). Emission is type-directed: each node is
;; rendered at its exact Swift type, so the output contains NO `Any` and NO
;; `as!` force-casts. The one existential is the exception payload — Swift's
;; own error channel is dynamically typed (`any Error`), and we mirror that
;; with `any Sendable` plus a safe `as?`, only at throw/catch boundaries.
;;
;; Semantic mapping (Swift is "eager": calling an async function starts it):
;;   async/lambda            -> @Sendable (A...) async throws -> R closure
;;   (f a...)  : (Task R)    -> Task<R, Error> { try await f(a...) }  (eager)
;;   (await t) / (os/block t): (t).value
;;   (os/io d v): (Task τ)   -> Task<τ, Error> { sleep(d); v }
;;   (cancel t): (Task τ)    -> __cancel(t)  (cancels, returns the task)
;;   (cancelled?)            -> Task.isCancelled
;; All functions compile to `async throws` closures (a sync `lambda` body may
;; still `await`, e.g. a recursive loop), so sync applications are awaited
;; inline and async applications are wrapped in an eager `Task`.
;;
;; `try`/`await` are placed exactly where an effect occurs (see `fx`), so the
;; output compiles warning-free.
;; -----------------------------------------------------------------------------

(require racket/match
         racket/string
         racket/format
         (only-in racket/list last drop-right))

(provide compile-swift)

(define preamble #<<EOF
// Compile with: swiftc -swift-version 6 -parse-as-library FILE.swift
import Foundation

struct Err: Error { let value: any Sendable }

final class Box<T>: @unchecked Sendable {
    var value: T
    init(_ v: T) { value = v }
}

func __throw<T>(_ v: any Sendable) throws -> T { throw Err(value: v) }

func __cancel<T>(_ t: Task<T, Error>) -> Task<T, Error> { t.cancel(); return t }

func __print(_ s: String) { print(s, terminator: "") }

EOF
)

(define (compile-swift ann)
  (define ty (ann-type ann))
  (string-append
   preamble "\n"
   "@main struct App {\n"
   "    static func main() async {\n"
   "        do {\n"
   (format "            let __result: ~a = ~a\n" (type->swift ty) (emit ann))
   "            print(__result)\n"
   "        } catch {\n"
   "            print(error)\n"
   "        }\n"
   "    }\n"
   "}\n"))

;; ---------------------------------------------------------------------------
;; Identifiers
;; ---------------------------------------------------------------------------

(define swift-keywords
  '("associatedtype" "class" "deinit" "enum" "extension" "fileprivate"
    "func" "import" "init" "inout" "internal" "let" "open" "operator"
    "private" "precedencegroup" "protocol" "public" "rethrows" "static"
    "struct" "subscript" "typealias" "var" "break" "case" "catch"
    "continue" "default" "defer" "do" "else" "fallthrough" "for" "guard"
    "if" "in" "repeat" "return" "switch" "throw" "try" "where" "while"
    "as" "false" "is" "nil" "self" "Self" "super" "throws" "true"
    "async" "await" "actor" "any" "nonisolated" "isolated"
    "Type" "Protocol" "result"))

(define (sanitize-var x)
  (define s (symbol->string x))
  (define cleaned (regexp-replace* #rx"[^a-zA-Z0-9_]" s "_"))
  (if (member cleaned swift-keywords)
      (string-append "`" cleaned "`")
      cleaned))

;; ---------------------------------------------------------------------------
;; Types
;; ---------------------------------------------------------------------------

(define (type->swift t)
  (match t
    ['Int "Int"]
    ['String "String"]
    ['Bool "Bool"]
    ['Unit "()"]
    [`(-> ,args ,ret)      (fn-type args ret)]
    [`(async-> ,args ,ret) (fn-type args ret)]
    [`(List ,t) (format "[~a]" (type->swift t))]
    [`(Box ,t) (format "Box<~a>" (type->swift t))]
    [`(Task ,t) (format "Task<~a, Error>" (type->swift t))]
    [_ (error 'compile-swift "no Swift type for: ~s" t)]))

;; All functions compile to async throws @Sendable closures.
(define (fn-type args ret)
  (format "@Sendable (~a) async throws -> ~a"
          (string-join (map type->swift args) ", ")
          (type->swift ret)))

(define (default-value t)
  (match t
    ['Int "0"]
    ['String "\"\""]
    ['Bool "false"]
    ['Unit "()"]
    [`(List ,_) "[]"]
    [_ (error 'compile-swift "no default for catch-handler arg type: ~s" t)]))

;; ---------------------------------------------------------------------------
;; Annotation helpers
;; ---------------------------------------------------------------------------

(define (ann-type a)
  (match a
    [`(: ,_ ,ty) ty]
    [`(typed-lambda ,ft ,_ ,_) ft]
    [`(typed-async-lambda ,ft ,_ ,_) ft]
    [_ (error 'compile-swift "unannotated node: ~s" a)]))

;; ---------------------------------------------------------------------------
;; Effects: does a node throw / await? (does not cross lambda or Task bodies)
;; Used to place `try`/`await` exactly, and to type immediately-invoked
;; closures (the `let`/`begin`/`if`/... IIFEs) as async/throws only when their
;; contents actually require it.
;; ---------------------------------------------------------------------------

(define pure (cons #f #f))
(define (fx-or . fs)
  (for/fold ([acc pure]) ([f (in-list fs)])
    (cons (or (car acc) (car f)) (or (cdr acc) (cdr f)))))
(define (fx-or* anns) (apply fx-or (map fx anns)))

(define (fx a)
  (match a
    [`(typed-lambda ,_ ,_ ,_) pure]        ; building a closure is pure
    [`(typed-async-lambda ,_ ,_ ,_) pure]
    [`(: ,form ,ty) (fx-form form ty)]
    [_ (error 'compile-swift "unannotated node: ~s" a)]))

(define (fx-form form ty)
  (match form
    [(? number?) pure] [(? string?) pure] [(? boolean?) pure] [(? symbol?) pure]
    [`(void) pure] [`(ptr ,_) pure] [`(cancelled?) pure] [`(os/time) pure]
    [`(os/io ,_ ,_) pure]                  ; Task { } construction is pure
    [(or `(await ,_) `(os/block ,_)) (cons #t #t)]
    [`(throw ,_) (cons #t #f)]
    [`(throw-in ,_ ,_) (cons #t #f)]
    [`(err ,_) (cons #t #f)]
    [`(catch ,_ ,_) (cons #t #t)]          ; handler may rethrow; body awaits
    [`(cancel ,t) (fx t)]
    [`(ok ,e) (fx e)]
    [`(if ,c ,t ,f) (fx-or (fx c) (fx t) (fx f))]
    [`(when ,c ,es ...) (fx-or* (cons c es))]
    [`(begin ,es ...) (fx-or* es)]
    [`(set! ,_ ,rhs) (fx rhs)]
    [`(let (,cs ...) ,body) (fx-or (fx-or* (map cadr cs)) (fx body))]
    [`(let* (,cs ...) ,body) (fx-or (fx-or* (map cadr cs)) (fx body))]
    [`(letrec (,cs ...) ,body)
     ;; lambda bindings are pure to create; only non-lambda rhss contribute
     (apply fx-or (fx body)
            (for/list ([c (in-list cs)])
              (match (cadr c)
                [(or `(typed-lambda ,_ ,_ ,_) `(typed-async-lambda ,_ ,_ ,_)) pure]
                [rhs (fx rhs)])))]
    ;; pure primitives: effects come only from operands
    [(or `(+ ,es ...) `(- ,es ...) `(list ,es ...) `(equal? ,es ...)
         `(string-append ,es ...))
     (fx-or* es)]
    [(or `(= ,a ,b) `(< ,a ,b) `(> ,a ,b) `(<= ,a ,b) `(>= ,a ,b) `(cons ,a ,b)
         `(set-box! ,a ,b))
     (fx-or (fx a) (fx b))]
    [(or `(number->string ,e) `(car ,e) `(cdr ,e) `(empty? ,e)
         `(box ,e) `(unbox ,e) `(print ,e) `(field ,_ ,e))
     (fx e)]
    ;; application
    [`(,f ,args ...)
     (match (ann-type f)
       [`(async-> ,_ ,_) pure]             ; Task { } construction is pure
       [`(-> ,_ ,_) (cons #t #t)])]        ; awaits the async closure
    [_ (error 'compile-swift "fx: unsupported form: ~s" form)]))

(define (call-prefix f)
  (string-append (if (car f) "try " "") (if (cdr f) "await " "")))
(define (sig f)
  (string-append (if (cdr f) " async" "") (if (car f) " throws" "")))

;; An immediately-invoked closure: `<prefix>{ ()<sig> -> T in <stmts> }()`,
;; typed and effect-tagged from `f`.
(define (iife ty f stmts)
  (format "~a{ ()~a -> ~a in ~a }()"
          (call-prefix f) (sig f) (type->swift ty) stmts))

;; ---------------------------------------------------------------------------
;; Emit (self-contained: each result already carries its own try/await)
;; ---------------------------------------------------------------------------

(define (emit a)
  (match a
    [(or `(typed-lambda ,ft ,xs ,body) `(typed-async-lambda ,ft ,xs ,body))
     (emit-fn ft xs body)]
    [`(: ,form ,ty) (emit-form form ty)]
    [_ (error 'compile-swift "unannotated node: ~s" a)]))

(define (emit-fn ft xs body)
  (match-define (or `(-> ,argtys ,rty) `(async-> ,argtys ,rty)) ft)
  (define params
    (string-join (map (lambda (x t) (format "_ ~a: ~a" (sanitize-var x) (type->swift t)))
                      xs argtys) ", "))
  (format "{ @Sendable (~a) async throws -> ~a in return ~a }"
          params (type->swift rty) (emit body)))

(define (emit-form form ty)
  (match form
    ;; --- Literals / atoms ---
    [(? number? n) (~a n)]
    [(? string? s) (~v s)]
    [#true "true"]
    [#false "false"]
    [`(void) "()"]
    [(? symbol? x) (sanitize-var x)]
    [`(ptr ,x) (sanitize-var x)]

    ;; --- Binding ---
    [`(let (,cs ...) ,body)  (emit-let cs body ty)]
    [`(let* (,cs ...) ,body) (emit-let cs body ty)]   ; sequential lets (see note)
    [`(letrec (,cs ...) ,body) (emit-letrec cs body ty)]

    ;; --- Sequencing / control ---
    [`(begin ,es ...) (emit-begin es ty)]
    [`(if ,c ,t ,f)
     (iife ty (fx-or (fx c) (fx t) (fx f))
           (format "if ~a { return ~a } else { return ~a }" (emit c) (emit t) (emit f)))]
    [`(when ,c ,es ...)
     (iife ty (fx-or* (cons c es))
           (format "if ~a { ~a }; return ()"
                   (emit c) (string-join (map discard-stmt es) "; ")))]
    [`(set! ,x ,rhs)
     (iife ty (fx rhs)
           (format "~a = ~a; return ~a" (sanitize-var x) (emit rhs) (sanitize-var x)))]

    ;; --- Print ---
    [`(print ,e) (format "__print(~a)" (emit e))]

    ;; --- Async ---
    [(or `(await ,t) `(os/block ,t)) (format "try await (~a).value" (emit t))]
    [`(os/io ,d ,v)
     (match-define `(Task ,vt) ty)
     (format "Task<~a, Error> { try await Task.sleep(nanoseconds: UInt64(~a) * 100_000_000); return ~a }"
             (type->swift vt) (emit d) (emit v))]
    [`(cancel ,t) (format "__cancel(~a)" (emit t))]
    [`(cancelled?) "Task.isCancelled"]
    [`(os/time) "Int(Date().timeIntervalSince1970 * 1000)"]

    ;; --- Exceptions ---
    [`(throw ,e)      (format "(try __throw(~a) as ~a)" (emit e) (type->swift ty))]
    [`(throw-in ,_ ,e) (format "(try __throw(~a) as ~a)" (emit e) (type->swift ty))]
    [`(catch ,handler ,body) (emit-catch handler body ty)]

    ;; --- Results ---
    [`(ok ,e) (emit e)]
    [`(err ,e) (format "(try __throw(~a) as ~a)" (emit e) (type->swift ty))]

    ;; --- Arithmetic / comparison / strings ---
    [`(+ ,es ...) (emit-binop "+" es "0")]
    [`(- ,es ...)
     (match es
       ['() "0"]
       [(list a) (format "(-~a)" (emit a))]
       [_ (format "(~a)" (string-join (map emit es) " - "))])]
    [`(= ,a ,b)  (format "(~a == ~a)" (emit a) (emit b))]
    [`(< ,a ,b)  (format "(~a < ~a)"  (emit a) (emit b))]
    [`(> ,a ,b)  (format "(~a > ~a)"  (emit a) (emit b))]
    [`(<= ,a ,b) (format "(~a <= ~a)" (emit a) (emit b))]
    [`(>= ,a ,b) (format "(~a >= ~a)" (emit a) (emit b))]
    [`(number->string ,e) (format "String(~a)" (emit e))]
    [`(equal? ,es ...)
     (match es
       [(or '() (list _)) "true"]
       [(list a b _ ...) (format "(~a == ~a)" (emit a) (emit b))])]
    [`(string-append ,es ...)
     (match es ['() "\"\""] [_ (format "(~a)" (string-join (map emit es) " + "))])]

    ;; --- Lists / boxes ---
    [`(list ,es ...) (format "[~a]" (string-join (map emit es) ", "))]
    [`(cons ,h ,t) (format "([~a] + ~a)" (emit h) (emit t))]
    [`(car ,e) (format "(~a)[0]" (emit e))]
    [`(cdr ,e) (format "Array((~a).dropFirst())" (emit e))]
    [`(empty? ,e) (format "(~a).isEmpty" (emit e))]
    [`(box ,e) (format "Box(~a)" (emit e))]
    [`(unbox ,e) (format "(~a).value" (emit e))]
    [`(set-box! ,a ,b)
     (iife ty (fx-or (fx a) (fx b))
           (format "(~a).value = ~a; return (~a).value" (emit a) (emit b) (emit a)))]

    ;; --- Application (must be last) ---
    [`(,f ,args ...) (emit-app f args ty)]

    [_ (error 'compile-swift "unsupported form: ~s" form)]))

(define (emit-binop op es identity)
  (match es
    ['() identity]
    [(list a) (emit a)]
    [_ (format "(~a)" (string-join (map emit es) (format " ~a " op)))]))

;; `let` and `let*` both compile to a sequence of Swift `let` bindings. A
;; type-checked `let` never has a clause whose rhs refers to a sibling (rhss
;; are typed in the outer scope), so sequential bindings preserve its meaning.
(define (emit-let cs body ty)
  (define f (fx-or (fx-or* (map cadr cs)) (fx body)))
  (define binds
    (string-join
     (for/list ([c (in-list cs)])
       (match-define (list x rhs) c)
       (format "let ~a: ~a = ~a" (sanitize-var x) (type->swift (ann-type rhs)) (emit rhs)))
     "; "))
  (iife ty f (format "~a; return ~a" binds (emit body))))

;; `letrec` binds (possibly mutually recursive) functions; emit them as nested
;; Swift funcs so they can reference themselves and each other.
(define (emit-letrec cs body ty)
  (define f
    (apply fx-or (fx body)
           (for/list ([c (in-list cs)])
             (match (cadr c)
               [(or `(typed-lambda ,_ ,_ ,_) `(typed-async-lambda ,_ ,_ ,_)) pure]
               [rhs (fx rhs)]))))
  (define decls
    (string-join
     (for/list ([c (in-list cs)])
       (match-define (list x rhs) c)
       (match rhs
         [(or `(typed-lambda (-> ,atys ,rty) ,xs ,b)
              `(typed-async-lambda (async-> ,atys ,rty) ,xs ,b))
          (define params
            (string-join (map (lambda (p t) (format "_ ~a: ~a" (sanitize-var p) (type->swift t)))
                              xs atys) ", "))
          (format "@Sendable func ~a(~a) async throws -> ~a { return ~a }"
                  (sanitize-var x) params (type->swift rty) (emit b))]
         [_ (format "let ~a: ~a = ~a" (sanitize-var x) (type->swift (ann-type rhs)) (emit rhs))]))
     "; "))
  (iife ty f (format "~a; return ~a" decls (emit body))))

(define (emit-begin es ty)
  (match es
    ['() "()"]
    [(list e) (emit e)]
    [_
     (define inits (string-join (map discard-stmt (drop-right es 1)) "; "))
     (iife ty (fx-or* es) (format "~a; return ~a" inits (emit (last es))))]))

;; A discarded statement: a Void-typed expression stands alone; anything else
;; is bound to `_` to silence the unused-result warning.
(define (discard-stmt e)
  (if (equal? (ann-type e) 'Unit)
      (emit e)
      (format "_ = ~a" (emit e))))

;; catch : Tb. handler : (Th) -> Tr  (Tr coincides with Tb in well-formed
;; programs). On an explicit throw the payload is recovered with a safe `as?`;
;; on cancellation (or any other error) the handler receives a default Th — our
;; handlers either ignore the argument or the thrown type already matches.
(define (emit-catch handler body ty)
  (match-define (or `(typed-lambda (-> (,th) ,_) ,_ ,_)
                    `(typed-async-lambda (async-> (,th) ,_) ,_ ,_)) handler)
  (define th-swift (type->swift th))
  (define dflt (default-value th))
  (format
   (string-append
    "try await { () async throws -> ~a in "
    "let __h = ~a; "
    "do { return ~a } "
    "catch let __e as Err { return try await __h((__e.value as? ~a) ?? ~a) } "
    "catch { return try await __h(~a) } }()")
   (type->swift ty) (emit handler) (emit body) th-swift dflt dflt))

(define (emit-app f args ty)
  (define fcode (emit f))
  (define argcode (string-join (map emit args) ", "))
  (match (ann-type f)
    [`(async-> ,_ ,R)
     ;; eager task: starts running, awaited later via .value
     (format "Task<~a, Error> { try await ~a(~a) }" (type->swift R) fcode argcode)]
    [`(-> ,_ ,_)
     (format "try await ~a(~a)" fcode argcode)]))
