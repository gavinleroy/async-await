#lang racket

(require redex)

;; -----------------------------------------------------------------------------
;; 1. Syntax and Language Definition
;; -----------------------------------------------------------------------------

(define-language AsyncLC
  (e ::=
     x                       
     v
     (+ e ...)
     (e e ...)               
     (if0 e e e)
     (fix e)
     #;(let* ([x e] ...) e)
     (lambda (x_!_ ...) e)
     (async/lambda (x_!_ ...) e )
     (await e)               
     (throw e)              
     (try e catch x e)
     
     #:binding-forms
     (lambda (x_!_ ...) e #:refers-to (shadow x ...))
     (async/lambda (x_!_ ...) e #:refers-to (shadow x ...))
     #;(let* ([x e] #:...bind (clauses x (shadow clauses x)))
       e_body #:refers-to clauses)
     )

  (v ::=
     number
     string
     (fix v)
     (lambda (x_!_ ...) e)          
     (async/lambda (x_!_ ...) e)    
     (task o)              
     (void))

  (E ::=
     hole
     (+ v ... E e ...)
     (v ... E e ...)
     (fix E)
     #;(let* ([x E] ...) e)
     (if E e e)
     (await E)
     (throw E)
     ;; Note: try/catch is a delimiter, so E does not recurse into it
     )

  (o ::= natural) ;; Heap object address

  (heap ::= (H (o task-state) ...))

  (task-state ::= (running (F ...)) (done v) (failed v))
  
  (L ::= (locals (x v)))

  (l ::= o sync)
  
  (F ::= (frame L e l))

  (FS ::= (stack F ...))

  (P ::= FS)

  (x y z ::= variable-not-otherwise-mentioned)
  )

;; -----------------------------------------------------------------------------
;; 2. Metafunctions (Substitution & Helpers)
;; -----------------------------------------------------------------------------

(define-metafunction AsyncLC
  subst : e x v -> e
  [(subst e x v) (substitute e x #:lang AsyncLC)])
  
(define-metafunction AsyncLC
  subst* : e (x v) ... e -> e
  [(subst* e (x v) ...)
   (substitute e (x v) ... #:lang AsyncLC)])

(define-metafunction AsyncLC
  fresh-id : store -> natural
  [(fresh-id ()) 0]
  [(fresh-id ((cell natural_id task-state) ...))
   ,(+ 1 (apply max (term (natural_id ...))))])

;; -----------------------------------------------------------------------------
;; 3. Operational Semantics
;; -----------------------------------------------------------------------------

(define -->C#
  (reduction-relation
   AsyncLC
   #:domain (H P)

   [--> (heap (stack (frame L (in-hole E ((lambda (x ..._1) e) v ..._1)) l) F_rest ...))
        (heap (stack (frame L (in-hole E (subst* e (x v) ...)) l) F_rest ...))
        "app"]

   #;
   [--> (heap (stack (frame (in-hole E (let ((x v)) e)) l) f_rest ...))
        (heap (stack (frame (in-hole E (subst x v e)) l) f_rest ...))
        "let"]

   #;[--> (heap (stack (frame L (in-hole E (if #t e_1 _)) l) f_rest ...))
        (heap (stack (frame L (in-hole E e_1) l) f_rest ...))
        "if-true"]

   #;[--> (heap (stack (frame L (in-hole E (if #f _ e_2)) l) f_rest ...))
        (heap (stack (frame L (in-hole E e_2) l) f_rest ...))
        "if-false"]

   ;; --------------------------------------------------------------------------
   ;; Async / Await Logic
   ;; --------------------------------------------------------------------------

   ;; When an async lambda is applied:
   ;; 1. Allocate a new task ID (new_tid).
   ;; 2. Modify the CURRENT frame to receive 'new_tid' as the result of the application.
   ;; 3. Push a NEW frame on top to execute the body of the async lambda.
   ;; This models the "synchronous start": the body runs immediately on the current thread.
   #;[--> (store (thread (frame (in-hole E ((async/lambda (x) e) v)) tid_curr) f_rest ...))
        (store_new
         (thread
          (frame (subst x v e) tid_new) ;; Push New Frame (Top)
          (frame (in-hole E (task tid_new)) tid_curr)
          f_rest ...))
        (where tid_new (fresh-id store))
        (where store_new (store-cons (cell tid_new (running ())) store))
        "app-async"]

   ;; When the top frame (associated with a task) finishes with a value:
   ;; 1. Update the task in the store to 'done'.
   ;; 3. Pop the completed frame from the stack.
   #;[--> (store (thread (frame (in-hole E v) tid_curr) f_rest ...))
        (store_new (thread f_rest ...))
        (side-condition (not (eq? (term tid_curr) (term sync))))
        (where store_new (store-cons (cell tid_curr (done v))
                                     (remove-task tid_curr store)))
        "async-return"]

   ;; [Await - Fast Path]
   ;; If the task is already done, unwrap the value and continue.
   #;[--> (store (thread (frame (in-hole E (await (task tid))) tid_curr) f_rest ...))
        (store (thread (frame (in-hole E v_val) tid_curr) f_rest ...))
        (where (done v_val) (lookup-task tid store))
        "await-fall-through"]

   ;; If the task is running:
   ;; 1. Capture the current context E as a frame.
   ;; 2. Store this frame in the Task's waiter list.
   ;; 3. Pop the current frame from the thread (Suspend).
   ;; 4. The thread continues executing the frame underneath (the caller).
   #;[--> (store (thread (frame (in-hole E (await (task tid))) tid_curr) f_rest ...))
        (store_new (thread f_rest ...)) ;; Pop and resume caller
        (where (running (f_wait ...)) (lookup-task tid store))
        (where store_new (store-cons (cell tid (running (f_wait ... (frame E tid_curr))))
                                     (remove-task tid store)))
        "await-suspend"]

   ;; --------------------------------------------------------------------------
   ;; Exceptions
   ;; --------------------------------------------------------------------------

   #;[--> (store (thread (frame (in-hole E (try (in-hole E (throw v)) catch x e_catch)) tid) f_rest ...))
        (store (thread (frame (in-hole E (subst x v e_catch)) tid) f_rest ...))
        "try-catch"]

   ;; If an exception bubbles to the top of an async frame:
   ;; 1. Fail the task.
   ;; 3. Pop frame.
   #;[--> (store (thread (frame (in-hole E (throw v_err)) tid) f_rest ...))
        (store_new (thread f_rest ... f_wait ...))
        (side-condition (not (eq? (term tid) (term sync))))
        (side-condition (not (term (in-try? E)))) ;; Ensure not caught locally
        (where (running (f_wait ...)) (lookup-task tid store))
        (where store_new (store-cons (cell tid (failed v_err))
                                     (remove-task tid store)))
        "async-fail"]

   ;; If awaiting a failed task, re-throw the exception.
   #;[--> (store (thread (frame (in-hole E (await (task tid))) tid_curr) f_rest ...))
        (store (thread (frame (in-hole E (throw v_err)) tid_curr) f_rest ...))
        (where (failed v_err) (lookup-task tid store))
        "await-failed"]
   ))

;; -----------------------------------------------------------------------------
;; 4. Helpers
;; -----------------------------------------------------------------------------

(define (program? t) (redex-match? AsyncLC P t))
(define (expr? t) (redex-match? AsyncLC e t))
(define (store? t) (redex-match? AsyncLC store t))

(define-metafunction AsyncLC
  meta-cons : any (any ...) -> (any ...)
  [(meta-cons any_0 (any_s ...))
   (any_0 any_s ...)])

(define-metafunction AsyncLC
  store-cons : l store -> store
  [(store-cons l store) (meta-cons l store)])

(define-metafunction AsyncLC
  lookup-task : natural store -> task-state
  [(lookup-task natural ((cell natural task-state) _ ...)) task-state]
  [(lookup-task natural (_ l_rest ...))
   (lookup-task natural (l_rest ...))])

(define-metafunction AsyncLC
  remove-task : natural store -> store
  [(remove-task natural ((cell natural task-state) l_rest ...)) (l_rest ...)]
  [(remove-task natural (l_0 l_rest ...))
   (store-cons l_0 (remove-task natural (l_rest ...)))]
  [(remove-task _ ()) ()])

(define-metafunction AsyncLC
  in-try? : E -> boolean
  [(in-try? hole) #f]
  [(in-try? (v E)) (in-try? E)]
  [(in-try? (E e)) (in-try? E)]
  [(in-try? (if E e e)) (in-try? E)]
  [(in-try? (let ((x E)) e)) (in-try? E)]
  [(in-try? (await E)) (in-try? E)]
  [(in-try? (throw E)) (in-try? E)]
  [(in-try? any) #f])

(define-metafunction AsyncLC
  main-c# : e -> P
  [(main-c# e) (() (thread (frame e sync)))])

(define-metafunction AsyncLC
  eval-c# : e -> v or stuck
  [(eval-c# e) (run-c# (main-c# e))])

(define-metafunction AsyncLC
  run-c# : P -> v or stuck
  [(run-c# (store (thread (frame v sync)))) v]
  [(run-c# any_1)
   (run-c# P_again)
   (where (P_again) ,(apply-reduction-relation -->C# (term any_1))) ]
  [(run-c# any)
   ,(begin
      (displayln (term any))
      (term stuck)
      ) ])

;; -----------------------------------------------------------------------------
;; 5. Traces
;; -----------------------------------------------------------------------------

(module+ test

  (test-equal (term (eval-c# 42))
              42)

  (test-equal (term (eval-c# ((lambda (x) x) 42)))
              42)

  (test-equal (term (eval-c# (let ([x 42]) 42)))
              42)

  (test-equal (term (eval-c# (let ([f (lambda (x) x)]) (f 42))))
              42)

  (test-equal (term (eval-c# (let ([f (async/lambda (x) x)])
                               (f 42))))
              (term (task 0)))

  (test-equal (term (eval-c# (let ([f (async/lambda (x) x)])
                               (await (f 42)))))
              42)

  (test-equal (term (eval-c# (let ([f (async/lambda (x) x)])
                               (let ([t (f 42)])
                                 (await t)))))
              42)
  )

(traces -->C# (term (main-c# (let ([f (async/lambda (x) x)])
                                (let ([t (f 42)])
                                  (await t))))))

#;
(stepper -->C#
         (term (main-c#
                (let ([f (async/lambda (x) x)])
                  (let ([t (f 42)])
                    (await t))))))

;; Simple test: Calling an async function that returns immediately
;; The trace should show the stack growing (app-async) then shrinking (return-async)
;; without actually suspending.
#;(traces -->C# (term (() ;; store
                       (thread
                        (frame
                         (let ((f (async/lambda (x) x)))
                           (let ((t (f 42)))
                             (await t)))
                         sync)))))

#;
(traces -->C#
        (term (() ;; store
               (thread
                (frame
                 (let ((f (async/lambda (x) x)))
                   (let ((t (f 42)))
                     (await t)))
                 sync)))))

;; Complex test: Interleaving
;; Function f awaits a value. Function main calls f, gets a task, does work, then awaits f.
#;
(traces -->C#
        (term (()
               (((frame

                  (hole
                   (let ((f (async/lambda (x)
                                          (if x
                                              10
                                              (await (async/lambda (y) 20) #t))))) ;; Inner async returns 20
                     (let ((t (f #f)))
                       (await t))))

                  sync))))))
