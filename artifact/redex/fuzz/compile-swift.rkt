#lang racket/base

(require racket/match
         racket/string
         racket/format
         (only-in racket/list last drop-right))

(provide compile-swift)

(define preamble #<<EOF
// Compile with: swiftc -swift-version 6 -parse-as-library FILE.swift
import Foundation

struct Err: Error, CustomStringConvertible {
    let value: Any
    var description: String { "\(value)" }
}

class Box {
    var value: Any
    init(_ v: Any) { value = v }
}

func __truthy(_ v: Any) -> Bool {
    if let b = v as? Bool { return b }
    return true
}

func __throw(_ e: Any) throws -> Any {
    throw Err(value: e)
}

func __tryCatch(_ body: () async throws -> Any, _ handler: (Any) async throws -> Any) async -> Any {
    do { return try await body() }
    catch let e as Err { return try! await handler(e.value) }
    catch { return try! await handler("\(error)") }
}

func __cons(_ h: Any, _ t: Any) -> [Any] {
    var l: [Any] = [h]
    l.append(contentsOf: t as! [Any])
    return l
}

func __seq(_ v: Any, _ next: () async throws -> Any) async rethrows -> Any { try await next() }

EOF
)

(define (compile-swift e)
  (string-append
   preamble "\n"
   "@main struct App {\n"
   "    static func main() async {\n"
   "        do {\n"
   "            let result: Any = try await " (emit e) "\n"
   "            print(result)\n"
   "        } catch {\n"
   "            print(error)\n"
   "        }\n"
   "    }\n"
   "}\n"))

(define swift-keywords
  '("associatedtype" "class" "deinit" "enum" "extension" "fileprivate"
    "func" "import" "init" "inout" "internal" "let" "open" "operator"
    "private" "precedencegroup" "protocol" "public" "rethrows" "static"
    "struct" "subscript" "typealias" "var" "break" "case" "catch"
    "continue" "default" "defer" "do" "else" "fallthrough" "for" "guard"
    "if" "in" "repeat" "return" "switch" "throw" "try" "where" "while"
    "as" "false" "is" "nil" "self" "Self" "super" "throws" "true"
    "async" "await" "actor" "any" "nonisolated" "isolated"
    "Type" "Protocol"))

(define (sanitize-var x)
  (define s (symbol->string x))
  (define cleaned (regexp-replace* #rx"[^a-zA-Z0-9_]" s "_"))
  (if (member cleaned swift-keywords)
      (string-append "`" cleaned "`")
      cleaned))

;; ---------------------------------------------------------------------------
;; Type rendering (Swift)
;; ---------------------------------------------------------------------------

(define (type->swift t)
  (match t
    ['Int "Int"]
    ['String "String"]
    ['Bool "Bool"]
    ['Unit "()"]
    [`(-> ,args ,ret)
     (format "@Sendable (~a) async throws -> ~a"
             (string-join (map type->swift args) ", ")
             (type->swift ret))]
    [`(async-> ,args ,ret)
     (format "@Sendable (~a) async throws -> ~a"
             (string-join (map type->swift args) ", ")
             (type->swift ret))]
    [`(List ,t) (format "[~a]" (type->swift t))]
    [`(Box ,t) (format "Box<~a>" (type->swift t))]
    [`(Task ,t) (format "Task<~a, Error>" (type->swift t))]
    [`(Struct ,_) "[String: Any]"]
    [_ "Any"]))

(define (fn-cast arity)
  (define params (make-list arity "Any"))
  (if (zero? arity)
      "() async throws -> Any"
      (format "(~a) async throws -> Any" (string-join params ", "))))

(define (make-list n v)
  (if (zero? n) '() (cons v (make-list (sub1 n) v))))

(define (emit-seq es)
  (if (= (length es) 1)
      (emit (car es))
      (format "try await __seq(~a, { ~a })" (emit (car es)) (emit-seq (cdr es)))))

(define (emit e)
  (match e
    ;; --- Literals ---
    [(? number? n) (format "(~a as Any)" n)]
    [(? string? s) (format "(~v as Any)" s)]
    [#true "(true as Any)"]
    [#false "(false as Any)"]
    [(? symbol? x) (sanitize-var x)]

    ;; --- Core forms ---
    [`(void) "(() as Any)"]
    [`(ptr ,x) (sanitize-var x)]

    [`(: ,inner ,_) (emit inner)]

    ;; --- Functions (typed) ---
    [`(typed-lambda (-> ,arg-types ,ret-type) ,xs ,body)
     (define arg-names (map (lambda (x) (string-append (sanitize-var x) "__arg")) xs))
     (define params (string-join (map (lambda (a t) (format "_ ~a: ~a" a (type->swift t))) arg-names arg-types) ", "))
     (define copies (string-join (map (lambda (x a) (format "var ~a = ~a;" (sanitize-var x) a)) xs arg-names) " "))
     (define rt (type->swift ret-type))
     (define ft (type->swift `(-> ,arg-types ,ret-type)))
     (format "({ (~a) async throws -> ~a in ~a return try ~a } as ~a)"
             params rt copies (emit body) ft)]

    [`(typed-async-lambda (async-> ,arg-types ,ret-type) ,xs ,body)
     (define arg-names (map (lambda (x) (string-append (sanitize-var x) "__arg")) xs))
     (define params (string-join (map (lambda (a t) (format "_ ~a: ~a" a (type->swift t))) arg-names arg-types) ", "))
     (define copies (string-join (map (lambda (x a) (format "var ~a = ~a;" (sanitize-var x) a)) xs arg-names) " "))
     (define rt (type->swift ret-type))
     (define ft (type->swift `(async-> ,arg-types ,ret-type)))
     (format "({ (~a) async throws -> ~a in ~a return try ~a } as ~a)"
             params rt copies (emit body) ft)]

    ;; --- Functions (untyped fallback) ---
    [`(lambda (,xs ...) ,body)
     (define arg-names (map (lambda (x) (string-append (sanitize-var x) "__arg")) xs))
     (define params (string-join (map (lambda (a) (format "_ ~a: Any" a)) arg-names) ", "))
     (define copies (string-join (map (lambda (x a) (format "var ~a = ~a;" (sanitize-var x) a)) xs arg-names) " "))
     (format "({ (~a) async throws -> Any in ~a return try ~a } as Any)"
             params copies (emit body))]

    [`(async/lambda (,xs ...) ,body)
     (define arg-names (map (lambda (x) (string-append (sanitize-var x) "__arg")) xs))
     (define params (string-join (map (lambda (a) (format "_ ~a: Any" a)) arg-names) ", "))
     (define copies (string-join (map (lambda (x a) (format "var ~a = ~a;" (sanitize-var x) a)) xs arg-names) " "))
     (format "({ (~a) async throws -> Any in ~a return try ~a } as Any)"
             params copies (emit body))]

    [`(letrec (,clauses ...) ,body)
     (define decls
       (for/list ([c (in-list clauses)])
         (match c
           [`(,x ,rhs) (format "var ~a: Any = () as Any; ~a = ~a;"
                                (sanitize-var x) (sanitize-var x) (emit rhs))]
           [_ ""])))
     (format "(try await { () async throws -> Any in ~a return try ~a }())"
             (string-join decls " ") (emit body))]

    ;; --- Binding (applied-closure pattern avoids async IIFE issues) ---
    [`(let (,clauses ...) ,body)
     (define xs (map (lambda (c) (match c [`(,x ,_) x])) clauses))
     (define rhss (map (lambda (c) (match c [`(,_ ,r) r])) clauses))
     (define arg-names (map (lambda (x) (string-append (sanitize-var x) "__arg")) xs))
     (define params (string-join (map (lambda (a) (format "_ ~a: Any" a)) arg-names) ", "))
     (define copies (string-join (map (lambda (x a) (format "var ~a = ~a;" (sanitize-var x) a)) xs arg-names) " "))
     (define args (string-join (map emit rhss) ", "))
     (format "(try await ({ (~a) async throws -> Any in ~a return try ~a })(~a))"
             params copies (emit body) args)]

    ;; --- Control flow ---
    [`(if ,c ,t ,f)
     (format "(__truthy(~a) ? try ~a : try ~a)" (emit c) (emit t) (emit f))]

    [`(begin ,es ...)
     (match es
       ['() "(() as Any)"]
       [(list e) (emit e)]
       [_ (emit-seq es)])]

    [`(set! ,x ,rhs)
     (format "(try await { () async throws -> Any in ~a = ~a; return ~a }())"
             (sanitize-var x) (emit rhs) (sanitize-var x))]

    ;; --- Async ---
    [`(await ,e)
     (emit e)]

    [`(os/block ,e)
     (emit e)]

    [`(os/io ,delay ,val)
     (format "(try await { () async throws -> Any in try await Task.sleep(nanoseconds: UInt64(~a) * 100_000_000); return ~a }())"
             (emit delay) (emit val))]

    [`(os/time)
     "(Int(Date().timeIntervalSince1970 * 1000) as Any)"]

    [`(os/start-soon ,e)
     (format "({ () -> Any in Task { let _ = try await ~a }; return () as Any }())"
             (emit e))]

    [`(os/start-later ,time ,_label ,e)
     (format "({ () -> Any in Task { try await Task.sleep(nanoseconds: UInt64(~a) * 100_000_000); let _ = try await ~a }; return () as Any }())"
             (emit time) (emit e))]

    ;; --- Cancellation (Swift-specific) ---
    [`(cancel ,e)
     (format "({ () -> Any in (~a as! Task<Any, Error>).cancel(); return () as Any }())"
             (emit e))]

    [`(cancelled?)
     "(Task.isCancelled as Any)"]

    ;; --- Exceptions ---
    [`(throw ,e)
     (format "(try __throw(~a))" (emit e))]

    [`(catch ,handler ,body)
     (format "(await __tryCatch({ try await ~a }, { (__e: Any) async throws -> Any in try await (~a as! ~a)(__e) }))"
             (emit body) (emit handler) (fn-cast 1))]

    [`(throw-in ,_coro ,exn)
     (format "(try __throw(~a))" (emit exn))]

    ;; --- Results ---
    [`(ok ,e) (emit e)]
    [`(err ,e) (format "(try __throw(~a))" (emit e))]

    ;; --- Arithmetic ---
    [`(+ ,es ...)
     (match es
       ['() "(0 as Any)"]
       [(list a) (emit a)]
       [_ (format "(~a as Any)"
                   (string-join (map (lambda (x) (format "(~a as! Int)" (emit x))) es) " + "))])]

    [`(- ,es ...)
     (match es
       ['() "(0 as Any)"]
       [(list a) (format "(-(~a as! Int) as Any)" (emit a))]
       [_ (format "(~a as Any)"
                   (string-join (map (lambda (x) (format "(~a as! Int)" (emit x))) es) " - "))])]

    [`(number->string ,e)
     (format "(String(describing: ~a) as Any)" (emit e))]

    ;; --- Comparison ---
    [`(= ,a ,b) (format "((~a as! Int) == (~a as! Int) as Any)" (emit a) (emit b))]
    [`(< ,a ,b) (format "((~a as! Int) < (~a as! Int) as Any)" (emit a) (emit b))]
    [`(> ,a ,b) (format "((~a as! Int) > (~a as! Int) as Any)" (emit a) (emit b))]
    [`(<= ,a ,b) (format "((~a as! Int) <= (~a as! Int) as Any)" (emit a) (emit b))]
    [`(>= ,a ,b) (format "((~a as! Int) >= (~a as! Int) as Any)" (emit a) (emit b))]

    ;; --- Strings ---
    [`(equal? ,es ...)
     (match es
       ['() "(true as Any)"]
       [(list _) "(true as Any)"]
       [(list a b) (format "(String(describing: ~a) == String(describing: ~a) as Any)" (emit a) (emit b))]
       [(list a b _ ...) (format "(String(describing: ~a) == String(describing: ~a) as Any)" (emit a) (emit b))])]

    [`(string-append ,es ...)
     (match es
       ['() "(\"\" as Any)"]
       [_ (format "(~a as Any)"
                   (string-join (map (lambda (x) (format "String(describing: ~a)" (emit x))) es) " + "))])]

    ;; --- Lists ---
    [`(list ,es ...)
     (format "([~a] as [Any] as Any)" (string-join (map emit es) ", "))]

    [`(cons ,h ,t)
     (format "(__cons(~a, ~a) as Any)" (emit h) (emit t))]

    [`(car ,e)
     (format "((~a as! [Any])[0])" (emit e))]

    [`(cdr ,e)
     (format "(Array((~a as! [Any]).dropFirst()) as Any)" (emit e))]

    [`(empty? ,e)
     (format "((~a as! [Any]).isEmpty as Any)" (emit e))]

    ;; --- Boxes ---
    [`(box ,e)
     (format "(Box(~a) as Any)" (emit e))]

    [`(unbox ,e)
     (format "((~a as! Box).value)" (emit e))]

    [`(set-box! ,a ,b)
     (format "(try await { () async throws -> Any in (~a as! Box).value = ~a; return (~a as! Box).value }())"
             (emit a) (emit b) (emit a))]

    ;; --- Structs ---
    [`(struct ,fields ...)
     (define pairs
       (for/list ([f (in-list fields)])
         (match f
           [`(,name ,val) (format "~s: ~a" (symbol->string name) (emit val))]
           [_ ""])))
     (format "([~a] as [String: Any] as Any)" (string-join pairs ", "))]

    [`(field ,name ,e)
     (format "((~a as! [String: Any])[~s]!)" (emit e) (symbol->string name))]

    ;; --- Application ---
    [`(,f ,args ...)
     (define-values (f-code f-cast arg-strs)
       (match f
         [`(: ,inner ,(and type (or `(-> ,arg-types ,_) `(async-> ,arg-types ,_))))
          (values (emit inner)
                  (type->swift type)
                  (map (λ (arg at) (format "(~a as! ~a)" (emit arg) (type->swift at)))
                       args arg-types))]
         [`(typed-lambda ,(and ft (or `(-> ,arg-types ,_) `(async-> ,arg-types ,_))) ,_ ,_)
          (values (emit f)
                  (type->swift ft)
                  (map (λ (arg at) (format "(~a as! ~a)" (emit arg) (type->swift at)))
                       args arg-types))]
         [_ (values (emit f) (fn-cast (length args)) (map emit args))]))
     (format "(try await (~a as! ~a)(~a))"
             f-code f-cast (string-join arg-strs ", "))]

    [_ (format "/* unhandled: ~s */ (() as Any)" e)]))
