#lang racket/base

;; -----------------------------------------------------------------------------
;; Rust backends: tokio and smol from one emitter (the `runtime` parameter).
;; Output is UNITYPED — every value is the Clone-able `Val` enum (closures
;; Arc'd, boxes Arc<Mutex<>>), so ownership never fights the model's
;; substitution semantics; variable reads clone.
;;
;; Semantic mapping, both runtimes ("lazy": applying an async fn builds an
;; un-polled future):
;;   async/lambda              -> Val::AsyncFn(move |args| Box::pin(async ...))
;;   (f a...)                  -> f.call(args)       (Val::Future, not polled)
;;   (spawn e)                 -> __spawn: runtime-spawn of e.do_await();
;;                                handle stored as Val::Task
;;   (await t), (os/block t)   -> t.do_await().await (join Task / poll Future)
;;   (os/io d v)               -> __io: runtime sleep(d ms); return v
;;
;; Runtime differences:
;;   tokio: (cancel t) -> JoinHandle::abort(); dropping a handle DETACHES the
;;          task; join surfaces {type: Ok|Err, value} (JoinError marks
;;          cancellation)
;;   smol:  (cancel t) -> Task::cancel().await; dropping a handle CANCELS the
;;          task (weak handles); join has no error channel (always Ok)
;; -----------------------------------------------------------------------------

(require racket/match
         racket/string
         racket/format
         (only-in racket/list last drop-right make-list remove-duplicates))

(provide compile-tokio compile-smol)

;; ---------------------------------------------------------------------------
;; Runtime parameter
;; ---------------------------------------------------------------------------

(define runtime (make-parameter 'tokio))

;; ---------------------------------------------------------------------------
;; Preamble construction
;; ---------------------------------------------------------------------------

(define preamble-common #<<EOF

type BoxFut = Pin<Box<dyn Future<Output = Val> + Send>>;

#[derive(Clone)]
enum Val {
    Int(i64),
    Str(String),
    Bool(bool),
    Unit,
    List(Vec<Val>),
    Boxed(Arc<Mutex<Val>>),
    Fn(Arc<dyn Fn(Vec<Val>) -> Val + Send + Sync>),
    AsyncFn(Arc<dyn Fn(Vec<Val>) -> BoxFut + Send + Sync>),
    Future(Arc<Mutex<Option<BoxFut>>>),
EOF
)

(define preamble-after-task #<<EOF
    Struct(HashMap<String, Val>),
}

impl std::fmt::Display for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Val::Int(n) => write!(f, "{}", n),
            Val::Str(s) => write!(f, "{}", s),
            Val::Bool(b) => write!(f, "{}", b),
            Val::Unit => write!(f, "()"),
            Val::List(l) => {
                write!(f, "(")?;
                for (i, v) in l.iter().enumerate() {
                    if i > 0 { write!(f, " ")?; }
                    write!(f, "{}", v)?;
                }
                write!(f, ")")
            }
            Val::Struct(m) => {
                write!(f, "{{")?;
                let mut first = true;
                for (k, v) in m {
                    if !first { write!(f, ", ")?; }
                    write!(f, "{}: {}", k, v)?;
                    first = false;
                }
                write!(f, "}}")
            }
            _ => write!(f, "#<opaque>"),
        }
    }
}

impl Val {
    fn as_int(&self) -> i64 {
        match self { Val::Int(n) => *n, _ => panic!("expected Int, got {}", self) }
    }
    fn as_bool(&self) -> bool {
        match self { Val::Bool(b) => *b, _ => panic!("expected Bool") }
    }
    fn as_list(&self) -> &[Val] {
        match self { Val::List(l) => l, _ => panic!("expected List") }
    }
    fn truthy(&self) -> bool {
        match self { Val::Bool(b) => *b, _ => true }
    }
    fn call(&self, args: Vec<Val>) -> Val {
        match self {
            Val::Fn(f) => f(args),
            Val::AsyncFn(f) => Val::Future(Arc::new(Mutex::new(Some(f(args))))),
            _ => panic!("not callable: {}", self),
        }
    }
EOF
)

(define preamble-helpers #<<EOF
}

fn __cons(h: Val, t: Val) -> Val {
    let tl = t.as_list();
    let mut l = Vec::with_capacity(1 + tl.len());
    l.push(h);
    l.extend_from_slice(tl);
    Val::List(l)
}

fn __car(l: &Val) -> Val { l.as_list()[0].clone() }
fn __cdr(l: &Val) -> Val { Val::List(l.as_list()[1..].to_vec()) }
fn __is_empty(l: &Val) -> Val { Val::Bool(l.as_list().is_empty()) }

fn __unbox(b: &Val) -> Val {
    match b { Val::Boxed(r) => r.lock().unwrap().clone(), _ => panic!("expected Box") }
}

fn __set_box(b: &Val, v: Val) -> Val {
    match b {
        Val::Boxed(r) => { *r.lock().unwrap() = v.clone(); v }
        _ => panic!("expected Box"),
    }
}

fn __field(s: &Val, name: &str) -> Val {
    match s {
        Val::Struct(m) => m.get(name).expect("field not found").clone(),
        _ => panic!("expected Struct"),
    }
}

fn __throw(e: Val) -> Val { panic!("{}", e) }

fn __print(v: Val) -> Val {
    use std::io::Write;
    print!("{}", v);
    std::io::stdout().flush().unwrap();
    Val::Unit
}

EOF
)

(define (make-preamble)
  (string-append
   ;; Header
   "#![allow(unused_mut, unused_variables, unreachable_code, dead_code, unused_imports)]\n"
   "use std::collections::HashMap;\n"
   "use std::future::Future;\n"
   "use std::pin::Pin;\n"
   "use std::sync::{Arc, Mutex};\n"
   "use std::time::Duration;\n"
   (case (runtime)
     [(tokio) "// Cargo.toml: tokio = { version = \"1\", features = [\"full\"] }\n"]
     [(smol)  "// Cargo.toml: smol = \"2\"\n"])
   ;; Val enum
   preamble-common "\n"
   (case (runtime)
     [(tokio) "    Task(Arc<Mutex<Option<tokio::task::JoinHandle<Val>>>>),\n"]
     [(smol)  "    Task(Arc<Mutex<Option<smol::Task<Val>>>>),\n"])
   preamble-after-task "\n"
   ;; do_await (runtime-specific Task branch)
   (case (runtime)
     ;; The mutex guard must be dropped before awaiting: holding it across
     ;; an await point makes the future non-Send, which tokio::spawn rejects.
     [(tokio) #<<EOF
    async fn do_await(self) -> Val {
        match self {
            Val::Future(f) => {
                let fut = f.lock().unwrap().take().expect("future consumed");
                fut.await
            }
            Val::Task(h) => {
                // JoinHandle::await -> Result<T, JoinError>, surfaced to the
                // program as a struct {type, value} (matches the model's
                // Ok/Err task-completion value).
                let handle = h.lock().unwrap().take().expect("task consumed");
                match handle.await {
                    Ok(v) => Val::Struct(HashMap::from([
                        ("type".to_string(), Val::Str("Ok".to_string())),
                        ("value".to_string(), v),
                    ])),
                    Err(e) if e.is_cancelled() => Val::Struct(HashMap::from([
                        ("type".to_string(), Val::Str("Err".to_string())),
                        ("value".to_string(), Val::Unit),
                    ])),
                    Err(e) => panic!("task failed: {}", e),
                }
            }
            other => other,
        }
    }
EOF
]
     [(smol) #<<EOF
    async fn do_await(self) -> Val {
        match self {
            Val::Future(f) => {
                let fut = f.lock().unwrap().take().expect("future consumed");
                fut.await
            }
            Val::Task(h) => {
                // smol Task::await -> T; the model wraps a joined task's value
                // as Ok(v), so surface the same struct {type, value}. (smol has
                // no JoinError; cancellation is handled on the cancel path.)
                let task = h.lock().unwrap().take().expect("task consumed");
                let v = task.await;
                Val::Struct(HashMap::from([
                    ("type".to_string(), Val::Str("Ok".to_string())),
                    ("value".to_string(), v),
                ]))
            }
            other => other,
        }
    }
EOF
])
   "\n"
   preamble-helpers
   ;; Runtime-specific functions
   (case (runtime)
     [(tokio) #<<EOF
async fn __spawn(v: Val) -> Val {
    let h = tokio::spawn(async move { v.do_await().await });
    Val::Task(Arc::new(Mutex::new(Some(h))))
}

fn __cancel(v: &Val) {
    if let Val::Task(h) = v {
        if let Some(handle) = h.lock().unwrap().as_ref() { handle.abort(); }
    }
}

async fn __io(delay: i64, val: Val) -> Val {
    tokio::time::sleep(Duration::from_millis(delay as u64)).await;
    val
}

EOF
]
     [(smol) #<<EOF
async fn __spawn(v: Val) -> Val {
    let t = smol::spawn(async move { v.do_await().await });
    Val::Task(Arc::new(Mutex::new(Some(t))))
}

async fn __cancel(v: &Val) {
    if let Val::Task(h) = v {
        // bind before awaiting: holding the MutexGuard across the await
        // point would make the future non-Send
        let task = h.lock().unwrap().take();
        if let Some(task) = task {
            let _ = task.cancel().await;
        }
    }
}

async fn __io(delay: i64, val: Val) -> Val {
    smol::Timer::after(Duration::from_millis(delay as u64)).await;
    val
}

EOF
])))

;; ---------------------------------------------------------------------------
;; Rust keywords
;; ---------------------------------------------------------------------------

(define rust-keywords
  '("as" "async" "await" "break" "const" "continue" "crate" "dyn" "else"
    "enum" "extern" "false" "fn" "for" "if" "impl" "in" "let" "loop"
    "match" "mod" "move" "mut" "pub" "ref" "return" "self" "Self" "static"
    "struct" "super" "trait" "true" "type" "unsafe" "use" "where" "while"
    "abstract" "become" "box" "do" "final" "macro" "override" "priv"
    "try" "typeof" "unsized" "virtual" "yield"))

(define (sanitize-var x)
  (define s (symbol->string x))
  (define cleaned (regexp-replace* #rx"[^a-zA-Z0-9_]" s "_"))
  (if (member cleaned rust-keywords)
      (string-append "r#" cleaned)
      cleaned))

;; ---------------------------------------------------------------------------
;; Environment helpers (for Rust closure capture)
;; ---------------------------------------------------------------------------

(define (clone-env env)
  (define unique (remove-duplicates (map sanitize-var env)))
  (if (null? unique) ""
      (string-append
       (string-join
        (map (λ (v) (format "let ~a = ~a.clone();" v v)) unique) " ")
       " ")))

(define (extract-lambda rhs)
  (match rhs
    [`(typed-lambda ,_ ,xs ,lb) (values xs lb #f)]
    [`(typed-async-lambda ,_ ,xs ,lb) (values xs lb #t)]
    [`(lambda (,xs ...) ,lb) (values xs lb #f)]
    [`(async/lambda (,xs ...) ,lb) (values xs lb #t)]
    [`(: ,inner ,_) (extract-lambda inner)]
    [_ (values #f rhs #f)]))

(define (make-params xs)
  (if (null? xs) ""
      (string-append
       (string-join
        (for/list ([x (in-list xs)] [i (in-naturals)])
          (format "let mut ~a = __args[~a].clone();" (sanitize-var x) i))
        " ")
       " ")))

;; ---------------------------------------------------------------------------
;; Emit
;; ---------------------------------------------------------------------------

(define (emit env e)
  (match e
    ;; --- Literals ---
    [(? number? n) (format "Val::Int(~a)" n)]
    [(? string? s) (format "Val::Str(~v.to_string())" s)]
    [#true "Val::Bool(true)"]
    [#false "Val::Bool(false)"]
    ;; Reads clone: a bare name is a MOVE in Rust, so a parameter passed to a
    ;; call and then returned (or any twice-used variable) is E0382. Val is
    ;; cheaply Clone (Arc'd innards); binding and assignment sites use
    ;; sanitize-var directly and stay bare.
    [(? symbol? x) (format "~a.clone()" (sanitize-var x))]

    ;; --- Core forms ---
    [`(void) "Val::Unit"]
    [`(ptr ,x) (sanitize-var x)]

    ;; --- Type annotations (strip) ---
    [`(: ,inner ,_) (emit env inner)]

    ;; --- Typed lambdas (delegate to untyped) ---
    [`(typed-lambda ,_ ,xs ,body)
     (emit env `(lambda ,xs ,body))]
    [`(typed-async-lambda ,_ ,xs ,body)
     (emit env `(async/lambda ,xs ,body))]

    ;; --- Lambda ---
    [`(lambda (,xs ...) ,body)
     (define new-env (append xs env))
     (define clones (clone-env env))
     (define params (make-params xs))
     (format "Val::Fn(Arc::new({ ~amove |__args: Vec<Val>| -> Val { ~a~a } }))"
             clones params (emit new-env body))]

    ;; --- Async lambda ---
    [`(async/lambda (,xs ...) ,body)
     (define new-env (append xs env))
     (define outer-clones (clone-env env))
     (define inner-clones (clone-env env))
     (define params (make-params xs))
     (format "Val::AsyncFn(Arc::new({ ~amove |__args: Vec<Val>| -> BoxFut { ~a~aBox::pin(async move { ~a }) } }))"
             outer-clones inner-clones params (emit new-env body))]

    ;; --- Letrec (cell-based self-reference via Arc<Mutex<>>) ---
    [`(letrec (,clauses ...) ,body)
     (define new-vars (map car clauses))
     (define new-env (append new-vars env))
     (define decls
       (for/list ([c (in-list clauses)])
         (match c
           [`(,x ,rhs)
            (define xn (sanitize-var x))
            (define-values (xs lbody is-async) (extract-lambda rhs))
            (if xs
                (let* ([cell (string-append xn "__cell")]
                       [inner-env (append xs (list x) env)]
                       [clones (clone-env env)]
                       [params (make-params xs)]
                       [deref (format "let ~a = ~a.lock().unwrap().clone().unwrap(); " xn cell)])
                  (string-append
                   (format "let ~a: Arc<Mutex<Option<Val>>> = Arc::new(Mutex::new(None)); " cell)
                   (if is-async
                       (format "let mut ~a = Val::AsyncFn(Arc::new({ let ~a = ~a.clone(); ~amove |__args: Vec<Val>| -> BoxFut { let ~a = ~a.clone(); ~a~aBox::pin(async move { ~a~a }) } })); "
                               xn cell cell clones
                               cell cell (clone-env env) params
                               deref (emit inner-env lbody))
                       (format "let mut ~a = Val::Fn(Arc::new({ let ~a = ~a.clone(); ~amove |__args: Vec<Val>| -> Val { ~a~a~a } })); "
                               xn cell cell clones
                               params deref (emit inner-env lbody)))
                   (format "*~a.lock().unwrap() = Some(~a.clone()); " cell xn)))
                (format "let mut ~a = ~a; " xn (emit env rhs)))]
           [_ ""])))
     (format "{ ~a~a }" (string-join decls "") (emit new-env body))]

    ;; --- Let ---
    [`(let (,clauses ...) ,body)
     (define decls
       (for/list ([c (in-list clauses)])
         (match c
           [`(,x ,rhs) (format "let mut ~a = ~a;" (sanitize-var x) (emit env rhs))]
           [_ ""])))
     (define new-vars (map car clauses))
     (define new-env (append new-vars env))
     (format "{ ~a ~a }" (string-join decls " ") (emit new-env body))]

    ;; --- Let* (each right-hand side sees the bindings before it) ---
    [`(let* (,clauses ...) ,body)
     (define-values (rev-decls new-env)
       (for/fold ([acc '()] [env env]) ([c (in-list clauses)])
         (match c
           [`(,x ,rhs)
            (values (cons (format "let mut ~a = ~a;" (sanitize-var x) (emit env rhs)) acc)
                    (cons x env))]
           [_ (values acc env)])))
     (format "{ ~a ~a }" (string-join (reverse rev-decls) " ") (emit new-env body))]

    ;; --- When ---
    [`(when ,c ,es ...)
     (format "if ~a.truthy() { ~a } else { Val::Unit }"
             (emit env c) (emit env `(begin ,@es (void))))]

    ;; --- Print (no newline) ---
    [`(print ,e)
     (format "__print(~a)" (emit env e))]

    ;; --- Control flow ---
    [`(if ,c ,t ,f)
     (format "if ~a.truthy() { ~a } else { ~a }"
             (emit env c) (emit env t) (emit env f))]

    [`(begin ,es ...)
     (match es
       ['() "Val::Unit"]
       [(list e) (emit env e)]
       [_
        (define stmts (drop-right es 1))
        (define last-e (last es))
        (format "{ ~a ~a }"
                (string-join (map (λ (s) (format "let _ = ~a;" (emit env s))) stmts) " ")
                (emit env last-e))])]

    [`(set! ,x ,rhs)
     (format "{ ~a = ~a; ~a.clone() }"
             (sanitize-var x) (emit env rhs) (sanitize-var x))]

    ;; --- Async ---
    [`(await ,e)
     (format "~a.do_await().await" (emit env e))]

    [`(os/block ,e)
     (format "~a.do_await().await" (emit env e))]

    [`(os/io ,delay ,val)
     (format "__io(~a.as_int(), ~a).await" (emit env delay) (emit env val))]

    [`(os/time)
     "Val::Int(std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_millis() as i64)"]

    [`(os/start-soon ,e)
     (emit env e)]

    [`(os/start-later ,_time ,_label ,e)
     (emit env e)]

    ;; --- Spawn / Cancel ---
    [`(spawn ,e)
     (format "__spawn(~a).await" (emit env e))]

    [`(cancel ,e)
     (case (runtime)
       [(tokio) (format "{ __cancel(&~a); Val::Unit }" (emit env e))]
       [(smol)  (format "{ __cancel(&~a).await; Val::Unit }" (emit env e))])]

    ;; --- Results ---
    [`(ok ,e) (emit env e)]
    [`(err ,e) (format "__throw(~a)" (emit env e))]

    ;; --- Arithmetic ---
    [`(+ ,es ...)
     (match es
       ['() "Val::Int(0)"]
       [(list a) (emit env a)]
       [_ (format "Val::Int(~a)"
                   (string-join (map (λ (x) (format "~a.as_int()" (emit env x))) es) " + "))])]

    [`(- ,es ...)
     (match es
       ['() "Val::Int(0)"]
       [(list a) (format "Val::Int(-~a.as_int())" (emit env a))]
       [_ (format "Val::Int(~a)"
                   (string-join (map (λ (x) (format "~a.as_int()" (emit env x))) es) " - "))])]

    [`(number->string ,e)
     (format "Val::Str(format!(\"{}\", ~a.as_int()))" (emit env e))]

    ;; --- Comparison ---
    [`(= ,a ,b)  (format "Val::Bool(~a.as_int() == ~a.as_int())" (emit env a) (emit env b))]
    [`(< ,a ,b)  (format "Val::Bool(~a.as_int() < ~a.as_int())"  (emit env a) (emit env b))]
    [`(> ,a ,b)  (format "Val::Bool(~a.as_int() > ~a.as_int())"  (emit env a) (emit env b))]
    [`(<= ,a ,b) (format "Val::Bool(~a.as_int() <= ~a.as_int())" (emit env a) (emit env b))]
    [`(>= ,a ,b) (format "Val::Bool(~a.as_int() >= ~a.as_int())" (emit env a) (emit env b))]

    ;; --- Strings ---
    [`(equal? ,es ...)
     (match es
       ['() "Val::Bool(true)"]
       [(list _) "Val::Bool(true)"]
       [(list a b)
        (format "Val::Bool(format!(\"{}\", ~a) == format!(\"{}\", ~a))"
                (emit env a) (emit env b))]
       [(list a b _ ...)
        (format "Val::Bool(format!(\"{}\", ~a) == format!(\"{}\", ~a))"
                (emit env a) (emit env b))])]

    [`(string-append ,es ...)
     (match es
       ['() "Val::Str(String::new())"]
       [_ (format "Val::Str(format!(\"~a\", ~a))"
                   (string-join (make-list (length es) "{}") "")
                   (string-join (map (λ (x) (emit env x)) es) ", "))])]

    ;; --- Lists ---
    [`(list ,es ...)
     (format "Val::List(vec![~a])" (string-join (map (λ (x) (emit env x)) es) ", "))]

    [`(cons ,h ,t)
     (format "__cons(~a, ~a)" (emit env h) (emit env t))]

    [`(car ,e)   (format "__car(&~a)" (emit env e))]
    [`(cdr ,e)   (format "__cdr(&~a)" (emit env e))]
    [`(empty? ,e) (format "__is_empty(&~a)" (emit env e))]

    ;; --- Boxes ---
    [`(box ,e)
     (format "Val::Boxed(Arc::new(Mutex::new(~a)))" (emit env e))]

    [`(unbox ,e)
     (format "__unbox(&~a)" (emit env e))]

    [`(set-box! ,a ,b)
     (format "__set_box(&~a, ~a)" (emit env a) (emit env b))]

    ;; --- Structs ---
    [`(struct ,fields ...)
     (define pairs
       (for/list ([f (in-list fields)])
         (match f
           [`(,name ,val)
            (format "(~v.to_string(), ~a)" (symbol->string name) (emit env val))]
           [_ ""])))
     (format "Val::Struct(HashMap::from([~a]))" (string-join pairs ", "))]

    [`(field ,name ,e)
     (format "__field(&~a, ~v)" (emit env e) (symbol->string name))]

    ;; --- Application ---
    [`(,f ,args ...)
     (define arg-exprs (map (λ (a) (emit env a)) args))
     (format "~a.call(vec![~a])" (emit env f) (string-join arg-exprs ", "))]

    [_ (format "Val::Unit /* unhandled: ~s */" e)]))

;; ---------------------------------------------------------------------------
;; Assemble
;; ---------------------------------------------------------------------------

(define (compile-with-runtime e)
  (define main-expr (emit '() e))
  (string-append
   (make-preamble) "\n"
   ;; print! (not println!): a mid-poll worker can print after block_on
   ;; returns, and the model's accumulator has no newline before such tail
   ;; prints -- a println! newline would make byte-identical tails
   ;; incomparable. Rust flushes stdout on clean exit.
   (case (runtime)
     [(tokio)
      (format "#[tokio::main]\nasync fn main() {\n    let result = ~a;\n    print!(\"{}\", result);\n}\n"
              main-expr)]
     [(smol)
      (format "fn main() {\n    smol::block_on(async {\n        let result = ~a;\n        print!(\"{}\", result);\n    })\n}\n"
              main-expr)])))

(define (compile-tokio e)
  (parameterize ([runtime 'tokio])
    (compile-with-runtime e)))

(define (compile-smol e)
  (parameterize ([runtime 'smol])
    (compile-with-runtime e)))
