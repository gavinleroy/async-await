#lang racket/base

;; -----------------------------------------------------------------------------
;; Python backends: asyncio and trio from one emitter (the `runtime`
;; parameter). Lambdas are hoisted to named top-level defs (Python lambdas
;; cannot contain statements); annotations become type hints.
;;
;; Semantic mapping, asyncio ("lazy": calling an async function builds a
;; coroutine; nothing runs until spawned or awaited):
;;   async/lambda              -> hoisted async def
;;   (f a...)                  -> f(a...)            (cold coroutine)
;;   (spawn c)                 -> asyncio.create_task(c)
;;   (await t), (os/block t)   -> (await t)
;;   (cancel t)                -> t.cancel()
;;   (os/io d v)               -> __io: await asyncio.sleep(d * 0.02); return v
;;
;; Semantic mapping, trio (also lazy; trio cancels scopes, never tasks, so
;; the only cancellation source is timeout):
;;   async/lambda              -> hoisted async def; each task body runs in
;;                                its own nursery (_TrioTask._run: task extent)
;;   (f a...)                  -> f(a...)            (cold coroutine)
;;   (spawn c)                 -> __spawn: _TrioTask started in the RUNNING
;;                                task's nursery (_current_nursery)
;;   (await t), (os/block t)   -> __await_task(t)    (result/event plumbing)
;;   (timeout d (spawn c))     -> __timeout: fresh nursery inside
;;                                trio.fail_after(d * 0.02); expiry cancels
;;                                the subtree, raises Exception("cancelled")
;;   (os/io d v)               -> __io: await trio.sleep(d * 0.02); return v
;; -----------------------------------------------------------------------------

(require racket/match
         racket/string
         racket/format
         (only-in racket/list last drop-right))

(provide compile-asyncio compile-trio)

;; ---------------------------------------------------------------------------
;; Preambles
;; ---------------------------------------------------------------------------

(define preamble-common #<<EOF

import inspect
import sys

def __print(s):
    sys.stdout.write(str(s))

class Box:
    def __init__(self, v): self.value = v

def __truthy(v):
    if isinstance(v, bool): return v
    return v is not False

def __throw(e):
    raise Exception(str(e))

async def __try_catch(body, handler):
    # BaseException: cancellation (asyncio.CancelledError, trio.Cancelled)
    # does not derive from Exception, but the models' `catch` intercepts it.
    try:
        r = body()
        return (await r) if inspect.isawaitable(r) else r
    except BaseException as e:
        r = handler(str(e))
        return (await r) if inspect.isawaitable(r) else r

def __cons(h, t):
    return [h] + list(t)

EOF
)

(define preamble-asyncio
  (string-append
   "import asyncio\n"
   preamble-common
   #<<EOF

# Model delays are logical units ordered by deadline, not durations; 20ms per
# unit keeps that ordering robust against loop jitter while letting a fuzz run
# finish in seconds instead of minutes (the JS backend gets the same numbers
# as setTimeout milliseconds).
async def __io(delay, val):
    await asyncio.sleep(delay * 0.02)
    return val

EOF
))

(define preamble-trio
  (string-append
   "import trio\nimport contextvars\n"
   preamble-common
   #<<EOF

# Result/event plumbing only — trio cancels scopes, never tasks, so the only
# cancellation source is __timeout.
class _TrioTask:
    def __init__(self):
        self._event = trio.Event()
        self._result = self._error = None

    # Task-extent structured concurrency, mirroring the model: one nursery
    # per task (children spawned anywhere during this task's execution live
    # at most as long as the task, and the task completes only after they do
    # -- the model's task:await-dependencies at task end). _current_nursery
    # is set in the task's OWN context: start_soon copies the spawner's
    # context, so the assignment cannot leak back into the spawner.
    async def _run(self, coro):
        try:
            async with trio.open_nursery() as nursery:
                _current_nursery.set(nursery)
                self._result = await coro
        except BaseException as e:
            # nurseries wrap exceptions in ExceptionGroup; unwrap
            # singletons so awaiters see the original error, matching the
            # model's task:set-failed! payload.
            while (isinstance(e, BaseExceptionGroup)
                   and len(e.exceptions) == 1):
                e = e.exceptions[0]
            self._error = e
        self._event.set()

    async def wait(self):
        await self._event.wait()
        if self._error: raise self._error
        return self._result

_current_nursery = contextvars.ContextVar('_current_nursery')

async def __spawn(coro):
    nursery = _current_nursery.get()
    task = _TrioTask()
    nursery.start_soon(task._run, coro)
    return task

async def __await_task(t):
    if isinstance(t, _TrioTask): return await t.wait()
    return await t

# Same logical-units-to-20ms scaling as the asyncio backend.
async def __io(delay, val):
    await trio.sleep(delay * 0.02)
    return val

# The deadline scope encloses a FRESH nursery hosting the timed task, so the
# child's own spawns live inside the scope and expiry cancels the whole
# subtree (the model's ancestor-walk flag). Running the coroutine inline
# would leave its spawns in the CALLER's nursery, outside the scope.
async def __timeout(d, coro):
    task = _TrioTask()
    try:
        with trio.fail_after(d * 0.02):
            async with trio.open_nursery() as n:
                n.start_soon(task._run, coro)
            return await task.wait()
    except trio.TooSlowError:
        raise Exception("cancelled")

EOF
))

;; ---------------------------------------------------------------------------
;; State: hoisted function definitions
;; ---------------------------------------------------------------------------

(define hoisted '())
(define counter 0)

(define (fresh-name prefix)
  (set! counter (add1 counter))
  (format "__~a_~a" prefix counter))

;; kind is 'sync, 'async, or 'async-nursery
;; ret is #f (untyped) or a string like "int" (typed)
(define (hoist! kind name params ret body-stmts)
  (set! hoisted (append hoisted (list (list kind name params ret body-stmts)))))

(define (reset-state!)
  (set! hoisted '())
  (set! counter 0))

;; ---------------------------------------------------------------------------
;; Python keywords
;; ---------------------------------------------------------------------------

(define py-keywords
  '("False" "None" "True" "and" "as" "assert" "async" "await" "break"
    "class" "continue" "def" "del" "elif" "else" "except" "finally"
    "for" "from" "global" "if" "import" "in" "is" "lambda" "nonlocal"
    "not" "or" "pass" "raise" "return" "try" "while" "with" "yield"))

(define (sanitize-var x)
  (define s (symbol->string x))
  (define cleaned (regexp-replace* #rx"[^a-zA-Z0-9_]" s "_"))
  (if (member cleaned py-keywords)
      (string-append cleaned "_")
      cleaned))

;; ---------------------------------------------------------------------------
;; Type rendering (Python)
;; ---------------------------------------------------------------------------

(define (type->py t)
  (match t
    ['Int "int"]
    ['String "str"]
    ['Bool "bool"]
    ['Unit "None"]
    [`(-> ,args ,ret)
     (format "Callable[[~a], ~a]"
             (string-join (map type->py args) ", ")
             (type->py ret))]
    [`(async-> ,args ,ret)
     (format "Callable[[~a], Coroutine[Any, Any, ~a]]"
             (string-join (map type->py args) ", ")
             (type->py ret))]
    [`(List ,t) (format "list[~a]" (type->py t))]
    [`(Box ,t) "Box"]
    [`(Task ,t)
     (case (runtime)
       [(trio) "_TrioTask"]
       [else (format "asyncio.Task[~a]" (type->py t))])]
    [`(Struct ,fields) "dict"]
    [_ "Any"]))

;; ---------------------------------------------------------------------------
;; Emit
;; ---------------------------------------------------------------------------

(define runtime (make-parameter 'asyncio))

(define (emit e)
  (match e
    ;; --- Literals ---
    [(? number? n) (~a n)]
    [(? string? s) (~v s)]
    [#true "True"]
    [#false "False"]
    [(? symbol? x) (sanitize-var x)]

    ;; --- Core forms ---
    [`(void) "None"]
    [`(ptr ,x) (sanitize-var x)]

    [`(: ,inner ,_) (emit inner)]

    ;; --- Functions (typed) ---
    [`(typed-lambda (-> ,arg-types ,ret-type) ,xs ,body)
     (define name (fresh-name "fn"))
     (define params
       (string-join (map (λ (x t) (format "~a: ~a" (sanitize-var x) (type->py t)))
                         xs arg-types) ", "))
     (hoist! 'sync name params (type->py ret-type) (format "return ~a" (emit body)))
     name]

    [`(typed-async-lambda (async-> ,arg-types ,ret-type) ,xs ,body)
     (define name (fresh-name "fn"))
     (define params
       (string-join (map (λ (x t) (format "~a: ~a" (sanitize-var x) (type->py t)))
                         xs arg-types) ", "))
     (hoist! 'async-nursery name params (type->py ret-type) (format "return ~a" (emit body)))
     name]

    ;; --- Functions (untyped fallback) ---
    [`(lambda (,xs ...) ,body)
     (define name (fresh-name "fn"))
     (define params (string-join (map sanitize-var xs) ", "))
     (hoist! 'sync name params #f (format "return ~a" (emit body)))
     name]

    [`(async/lambda (,xs ...) ,body)
     (define name (fresh-name "fn"))
     (define params (string-join (map sanitize-var xs) ", "))
     (hoist! 'async-nursery name params #f (format "return ~a" (emit body)))
     name]

    [`(letrec (,clauses ...) ,body)
     (define non-fn-assigns '())
     (for ([c (in-list clauses)])
       (match c
         [`(,x (typed-lambda (-> ,arg-types ,ret-type) ,xs ,lbody))
          (define params
            (string-join (map (λ (xi t) (format "~a: ~a" (sanitize-var xi) (type->py t)))
                              xs arg-types) ", "))
          (hoist! 'sync (sanitize-var x) params (type->py ret-type)
                  (format "return ~a" (emit lbody)))]
         [`(,x (typed-async-lambda (async-> ,arg-types ,ret-type) ,xs ,lbody))
          (define params
            (string-join (map (λ (xi t) (format "~a: ~a" (sanitize-var xi) (type->py t)))
                              xs arg-types) ", "))
          (hoist! 'async-nursery (sanitize-var x) params (type->py ret-type)
                  (format "return ~a" (emit lbody)))]
         [`(,x ,rhs)
          ;; Bind at module scope: hoisted function bodies resolve their free
          ;; variables there, and a walrus binding would be local to __main.
          (set! non-fn-assigns
                (append non-fn-assigns
                        (list (format "globals().__setitem__('~a', ~a)"
                                      (sanitize-var x) (emit rhs)))))]))
     (if (null? non-fn-assigns)
         (emit body)
         (format "(~a, ~a)[-1]"
                 (string-join non-fn-assigns ", ")
                 (emit body)))]

    ;; --- Binding ---
    ;; Both routes go through letrec: walrus assignments are already
    ;; sequential (so let = let*), and letrec hoists function bindings as
    ;; named top-level defs — a walrus-bound function would be invisible to
    ;; other hoisted function bodies (Python resolves their free variables
    ;; at module scope).
    [`(let (,clauses ...) ,body)
     (emit `(letrec ,clauses ,body))]

    [`(let* (,clauses ...) ,body)
     (emit `(letrec ,clauses ,body))]

    ;; --- When ---
    [`(when ,c ,es ...)
     (emit `(if ,c (begin ,@es (void)) (void)))]

    ;; --- Print (no newline) ---
    [`(print ,e)
     (format "__print(~a)" (emit e))]

    ;; --- Control flow ---
    [`(if ,c ,t ,f)
     (format "(~a if __truthy(~a) else ~a)" (emit t) (emit c) (emit f))]

    [`(begin ,es ...)
     (match es
       ['() "None"]
       [(list e) (emit e)]
       [_ (format "(~a)[-1]" (string-join (map emit es) ", "))])]

    [`(set! ,x ,rhs)
     (format "(~a := ~a)" (sanitize-var x) (emit rhs))]

    ;; --- Async ---
    [`(await ,e)
     (case (runtime)
       [(trio) (format "(await __await_task(~a))" (emit e))]
       [else (format "(await ~a)" (emit e))])]

    [`(os/block ,e)
     (format "(await ~a)" (emit e))]

    [`(os/io ,delay ,val)
     (format "__io(~a, ~a)" (emit delay) (emit val))]

    [`(os/time)
     "int(__import__('time').time() * 1000)"]

    [`(os/start-soon ,e)
     (emit e)]

    [`(os/start-later ,_time ,_label ,e)
     (emit e)]

    ;; --- Spawn / Cancel / Timeout ---
    [`(spawn ,e)
     (case (runtime)
       [(asyncio) (format "asyncio.create_task(~a)" (emit e))]
       [(trio) (format "(await __spawn(~a))" (emit e))])]

    [`(cancel ,e)
     (format "(~a).cancel()" (emit e))]

    ;; trio: the timed coroutine becomes a task inside __timeout's scoped
    ;; nursery (see the preamble). Only the (timeout d (spawn coro)) shape is
    ;; generated; the spawn node may arrive annotation-wrapped.
    [`(timeout ,d ,inner)
     (define coro
       (match inner
         [`(spawn ,c) c]
         [`(: (spawn ,c) ,_) c]
         [_ (error 'compile-py "timeout of a non-spawn shape: ~s" inner)]))
     (format "(await __timeout(~a, ~a))" (emit d) (emit coro))]

    ;; --- Exceptions ---
    [`(throw ,e)
     (format "__throw(~a)" (emit e))]

    [`(catch ,handler ,body)
     (define body-name (fresh-name "catch_body"))
     (hoist! 'async body-name "" #f (format "return ~a" (emit body)))
     (format "(await __try_catch(~a, ~a))" body-name (emit handler))]

    [`(throw-in ,_coro ,exn)
     (format "__throw(~a)" (emit exn))]

    ;; --- Results ---
    [`(ok ,e) (emit e)]
    [`(err ,e) (format "__throw(~a)" (emit e))]

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
     (format "str(~a)" (emit e))]

    ;; --- Comparison ---
    [`(= ,a ,b) (format "(~a == ~a)" (emit a) (emit b))]
    [`(< ,a ,b) (format "(~a < ~a)" (emit a) (emit b))]
    [`(> ,a ,b) (format "(~a > ~a)" (emit a) (emit b))]
    [`(<= ,a ,b) (format "(~a <= ~a)" (emit a) (emit b))]
    [`(>= ,a ,b) (format "(~a >= ~a)" (emit a) (emit b))]

    ;; --- Strings ---
    [`(equal? ,es ...)
     (match es
       ['() "True"]
       [(list _) "True"]
       [(list a b) (format "(~a == ~a)" (emit a) (emit b))]
       [(list a b _ ...) (format "(~a == ~a)" (emit a) (emit b))])]

    [`(string-append ,es ...)
     (match es
       ['() "\"\""]
       [_ (format "(~a)" (string-join (map (lambda (x) (format "str(~a)" (emit x))) es) " + "))])]

    ;; --- Lists ---
    [`(list ,es ...)
     (format "[~a]" (string-join (map emit es) ", "))]

    [`(cons ,h ,t)
     (format "__cons(~a, ~a)" (emit h) (emit t))]

    [`(car ,e) (format "(~a)[0]" (emit e))]
    [`(cdr ,e) (format "(~a)[1:]" (emit e))]
    [`(empty? ,e) (format "(len(~a) == 0)" (emit e))]

    ;; --- Boxes ---
    [`(box ,e) (format "Box(~a)" (emit e))]
    [`(unbox ,e) (format "(~a).value" (emit e))]

    [`(set-box! ,a ,b)
     (define va (emit a))
     (format "(setattr(~a, 'value', ~a) or ~a.value)" va (emit b) va)]

    ;; --- Structs ---
    [`(struct ,fields ...)
     (define pairs
       (for/list ([f (in-list fields)])
         (match f
           [`(,name ,val) (format "~s: ~a" (symbol->string name) (emit val))]
           [_ ""])))
     (format "{~a}" (string-join pairs ", "))]

    [`(field ,name ,e)
     (format "(~a)[~s]" (emit e) (symbol->string name))]

    ;; --- Application (no auto-await: caller decides via await/spawn) ---
    [`(,f ,args ...)
     (format "~a(~a)" (emit f) (string-join (map emit args) ", "))]

    [_ (format "None  # unhandled: ~s" e)]))

;; ---------------------------------------------------------------------------
;; Assemble
;; ---------------------------------------------------------------------------

(define (render-hoisted)
  (define (ret-ann ret) (if ret (format " -> ~a" ret) ""))
  (string-join
   (for/list ([h (in-list hoisted)])
     (match h
       ;; Task-extent (trio): helper functions do NOT open nurseries -- the
       ;; only nurseries are per-task (_TrioTask._run) and the entry's
       ;; (__trio_entry). A helper's spawns attach to the RUNNING task's
       ;; nursery via _current_nursery, so a spawned task may outlive the
       ;; function that spawned it but never its spawning task.
       [(list 'async-nursery name params ret body)
        (define sig (if (string=? params "")
                        (format "async def ~a()~a:" name (ret-ann ret))
                        (format "async def ~a(~a)~a:" name params (ret-ann ret))))
        (string-append sig "\n" (format "    ~a\n" body))]
       [(list 'async name params ret body)
        (define ra (ret-ann ret))
        (if (string=? params "")
            (format "async def ~a()~a:\n    ~a\n" name ra body)
            (format "async def ~a(~a)~a:\n    ~a\n" name params ra body))]
       [(list 'sync name params ret body)
        (define ra (ret-ann ret))
        (if (string=? params "")
            (format "def ~a()~a:\n    ~a\n" name ra body)
            (format "def ~a(~a)~a:\n    ~a\n" name params ra body))]))
   "\n"))

(define (compile-with-runtime rt preamble e)
  (reset-state!)
  (parameterize ([runtime rt])
    (define main-expr (emit e))
    (define hoisted-str (render-hoisted))
    (string-append
     preamble "\n"
     hoisted-str "\n"
     (format "async def __main():\n    return ~a\n\n" main-expr)
     (case rt
       [(asyncio) "print(asyncio.run(__main()))\n"]
       [(trio)
        (string-append
         "async def __trio_entry():\n"
         "    async with trio.open_nursery() as __nursery:\n"
         "        _current_nursery.set(__nursery)\n"
         (format "        return ~a\n\n" main-expr)
         "print(trio.run(__trio_entry))\n")]))))

(define (compile-asyncio e)
  (compile-with-runtime 'asyncio preamble-asyncio e))

(define (compile-trio e)
  (compile-with-runtime 'trio preamble-trio e))
