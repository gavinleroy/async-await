#lang racket/base

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

class Box {
    public dynamic Value;
    public Box(dynamic v) { Value = v; }
}

class Program {
    static bool __truthy(dynamic v) { return !Object.Equals(v, false); }

    static dynamic __throw(dynamic e) {
        throw new Exception(e?.ToString() ?? "error");
    }

    static dynamic __tryCatch(Func<dynamic> body, dynamic handler) {
        try { return body(); }
        catch (Exception e) { return ((dynamic)handler)((dynamic)e.Message); }
    }

    static List<dynamic> __cons(dynamic h, dynamic t) {
        var l = new List<dynamic> { h };
        l.AddRange((List<dynamic>)t);
        return l;
    }

EOF
)

(define (compile-cs e)
  (string-append
   preamble
   "    static async Task Main() {\n"
   "        try {\n"
   "            dynamic result = " (emit e) ";\n"
   "            Console.WriteLine(result);\n"
   "        } catch (Exception e) {\n"
   "            Console.Error.WriteLine(e.Message);\n"
   "        }\n"
   "    }\n"
   "}\n"))

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

(define (sanitize-var x)
  (define s (symbol->string x))
  (define cleaned (regexp-replace* #rx"[^a-zA-Z0-9_]" s "_"))
  (if (member cleaned cs-keywords)
      (string-append "@" cleaned)
      cleaned))

(define (func-type arity)
  (define params (make-list (add1 arity) "dynamic"))
  (format "Func<~a>" (string-join params ", ")))

(define (async-func-type arity)
  (if (zero? arity)
      "Func<Task<dynamic>>"
      (let ([params (make-list arity "dynamic")])
        (format "Func<~a, Task<dynamic>>" (string-join params ", ")))))

(define (make-list n v)
  (if (zero? n) '() (cons v (make-list (sub1 n) v))))

;; ---------------------------------------------------------------------------
;; Type rendering (C#)
;; ---------------------------------------------------------------------------

(define (type->cs t)
  (match t
    ['Int "int"]
    ['String "string"]
    ['Bool "bool"]
    ['Unit "object"]
    [`(-> ,args ,ret)
     (define all (append (map type->cs args) (list (type->cs ret))))
     (format "Func<~a>" (string-join all ", "))]
    [`(async-> ,args ,ret)
     (define all (append (map type->cs args) (list (format "Task<~a>" (type->cs ret)))))
     (format "Func<~a>" (string-join all ", "))]
    [`(List ,t) (format "List<~a>" (type->cs t))]
    [`(Box ,_) "Box"]
    [`(Task ,t) (format "Task<~a>" (type->cs t))]
    [`(Struct ,_) "Dictionary<string, dynamic>"]
    [_ "dynamic"]))

(define (emit e)
  (match e
    ;; --- Literals ---
    [(? number? n) (format "(dynamic)~a" n)]
    [(? string? s) (~v s)]
    [#true "(dynamic)true"]
    [#false "(dynamic)false"]
    [(? symbol? x) (sanitize-var x)]

    ;; --- Core forms ---
    [`(void) "(dynamic)null"]
    [`(ptr ,x) (sanitize-var x)]

    [`(: ,inner ,_) (emit inner)]

    ;; --- Functions (typed) ---
    [`(typed-lambda (-> ,arg-types ,ret-type) ,xs ,body)
     (define params
       (string-join (map (λ (x t) (format "~a ~a" (type->cs t) (sanitize-var x)))
                         xs arg-types) ", "))
     (define ft (append (map type->cs arg-types) (list (type->cs ret-type))))
     (format "((Func<~a>)((~a) => ~a))"
             (string-join ft ", ") params (emit body))]

    [`(typed-async-lambda (async-> ,arg-types ,ret-type) ,xs ,body)
     (define params
       (string-join (map (λ (x t) (format "~a ~a" (type->cs t) (sanitize-var x)))
                         xs arg-types) ", "))
     (define ft (append (map type->cs arg-types) (list (format "Task<~a>" (type->cs ret-type)))))
     (format "((Func<~a>)(async (~a) => ~a))"
             (string-join ft ", ") params (emit body))]

    ;; --- Functions (untyped fallback) ---
    [`(lambda (,xs ...) ,body)
     (define params
       (string-join (map (lambda (x) (format "dynamic ~a" (sanitize-var x))) xs) ", "))
     (format "((~a)((~a) => ~a))"
             (func-type (length xs)) params (emit body))]

    [`(async/lambda (,xs ...) ,body)
     (define params
       (string-join (map (lambda (x) (format "dynamic ~a" (sanitize-var x))) xs) ", "))
     (format "((~a)(async (~a) => ~a))"
             (async-func-type (length xs)) params (emit body))]

    [`(letrec (,clauses ...) ,body)
     (define decls
       (for/list ([c (in-list clauses)])
         (match c
           [`(,x ,rhs) (format "dynamic ~a = ~a;" (sanitize-var x) (emit rhs))]
           [_ ""])))
     (format "((Func<dynamic>)(() => { ~a return ~a; }))()"
             (string-join decls " ")
             (emit body))]

    ;; --- Binding ---
    [`(let (,clauses ...) ,body)
     (define decls
       (for/list ([c (in-list clauses)])
         (match c
           [`(,x ,rhs) (format "dynamic ~a = ~a;" (sanitize-var x) (emit rhs))]
           [_ ""])))
     (format "((Func<dynamic>)(() => { ~a return ~a; }))()"
             (string-join decls " ")
             (emit body))]

    ;; --- Control flow ---
    [`(if ,c ,t ,f)
     (format "(__truthy(~a) ? ~a : ~a)" (emit c) (emit t) (emit f))]

    [`(begin ,es ...)
     (match es
       ['() "(dynamic)null"]
       [(list e) (emit e)]
       [_
        (define stmts (map emit (drop-right es 1)))
        (define last-e (emit (last es)))
        (format "((Func<dynamic>)(() => { ~a return ~a; }))()"
                (string-join (map (lambda (s) (string-append s ";")) stmts) " ")
                last-e)])]

    [`(set! ,x ,rhs)
     (format "(~a = ~a)" (sanitize-var x) (emit rhs))]

    ;; --- Async ---
    [`(await ,e)
     (format "(await (dynamic)~a)" (emit e))]

    [`(os/block ,e)
     (format "(await (dynamic)~a)" (emit e))]

    [`(os/io ,delay ,val)
     (format "(await ((Func<Task<dynamic>>)(async () => { await Task.Delay((int)~a); return ~a; }))())"
             (emit delay) (emit val))]

    [`(os/time)
     "(dynamic)DateTimeOffset.UtcNow.ToUnixTimeMilliseconds()"]

    [`(os/start-soon ,e)
     (format "((Func<dynamic>)(() => { Task.Run(() => ~a); return (dynamic)null; }))()"
             (emit e))]

    [`(os/start-later ,time ,_label ,e)
     (format "((Func<dynamic>)(() => { Task.Delay((int)~a).ContinueWith(_ => ~a); return (dynamic)null; }))()"
             (emit time) (emit e))]

    ;; --- Exceptions ---
    [`(throw ,e)
     (format "__throw(~a)" (emit e))]

    [`(catch ,handler ,body)
     (format "__tryCatch(() => ~a, ~a)"
             (emit body) (emit handler))]

    [`(throw-in ,_coro ,exn)
     (format "__throw(~a)" (emit exn))]

    ;; --- Results ---
    [`(ok ,e) (emit e)]
    [`(err ,e) (format "__throw(~a)" (emit e))]

    ;; --- Arithmetic ---
    [`(+ ,es ...)
     (match es
       ['() "(dynamic)0"]
       [(list a) (emit a)]
       [_ (format "(~a)" (string-join (map emit es) " + "))])]

    [`(- ,es ...)
     (match es
       ['() "(dynamic)0"]
       [(list a) (format "(-(dynamic)~a)" (emit a))]
       [_ (format "(~a)" (string-join (map emit es) " - "))])]

    [`(number->string ,e)
     (format "((dynamic)~a).ToString()" (emit e))]

    ;; --- Comparison ---
    [`(= ,a ,b) (format "(dynamic)(~a == ~a)" (emit a) (emit b))]
    [`(< ,a ,b) (format "(dynamic)(~a < ~a)" (emit a) (emit b))]
    [`(> ,a ,b) (format "(dynamic)(~a > ~a)" (emit a) (emit b))]
    [`(<= ,a ,b) (format "(dynamic)(~a <= ~a)" (emit a) (emit b))]
    [`(>= ,a ,b) (format "(dynamic)(~a >= ~a)" (emit a) (emit b))]

    ;; --- Strings ---
    [`(equal? ,es ...)
     (match es
       ['() "(dynamic)true"]
       [(list _) "(dynamic)true"]
       [(list a b) (format "(dynamic)Object.Equals(~a, ~a)" (emit a) (emit b))]
       [(list a b _ ...) (format "(dynamic)Object.Equals(~a, ~a)" (emit a) (emit b))])]

    [`(string-append ,es ...)
     (match es
       ['() "(dynamic)\"\""]
       [_ (format "(~a)"
                   (string-join (map (lambda (x) (format "(~a)?.ToString() ?? \"\"" (emit x))) es)
                                " + "))])]

    ;; --- Lists ---
    [`(list ,es ...)
     (format "new List<dynamic> { ~a }" (string-join (map emit es) ", "))]

    [`(cons ,h ,t)
     (format "__cons(~a, ~a)" (emit h) (emit t))]

    [`(car ,e)
     (format "((List<dynamic>)~a)[0]" (emit e))]

    [`(cdr ,e)
     (format "(dynamic)((List<dynamic>)~a).Skip(1).ToList()" (emit e))]

    [`(empty? ,e)
     (format "(dynamic)(((List<dynamic>)~a).Count == 0)" (emit e))]

    ;; --- Boxes ---
    [`(box ,e)
     (format "new Box(~a)" (emit e))]

    [`(unbox ,e)
     (format "((Box)~a).Value" (emit e))]

    [`(set-box! ,a ,b)
     (format "(((Box)~a).Value = ~a)" (emit a) (emit b))]

    ;; --- Structs ---
    [`(struct ,fields ...)
     (define pairs
       (for/list ([f (in-list fields)])
         (match f
           [`(,name ,val) (format "{ ~s, ~a }" (symbol->string name) (emit val))]
           [_ ""])))
     (format "new Dictionary<string, dynamic> { ~a }" (string-join pairs ", "))]

    [`(field ,name ,e)
     (format "((Dictionary<string, dynamic>)~a)[~s]" (emit e) (symbol->string name))]

    ;; --- Application ---
    [`(,f ,args ...)
     (format "((dynamic)~a)(~a)" (emit f) (string-join (map emit args) ", "))]

    [_ (format "/* unhandled: ~s */ (dynamic)null" e)]))
