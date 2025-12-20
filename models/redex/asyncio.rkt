#lang racket

(require redex
         "platform.rkt"
         "lc.rkt"
         "lc+exn.rkt"
         "lc+coro.rkt"
         "python.rkt")

(define-extended-language AsyncIO/Core Python

  (e ::= ....
     (spawn e)
     (cancel e)
     (run e))
  
  (v ::= ....
     (task x_async))
  
  (E ::= ....
     (spawn E)
     (cancel E)
     (run E)))

(define-event-loop
  AsyncIO AsyncIO/Core)

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->base
  (extend-reduction-relation -->py AsyncIO))

(define -->aio
  (reduction-relation
   AsyncIO #:domain (t σ Q P)

   ;; start task

   [--> (t_0 σ_0 Q_0 (FS_0 ... (stack (frame (in-hole E (spawn v_coro)) l) F ...) FS_1 ...))
        (t_1 σ_1 Q_1 (FS_0 ... (stack (frame (in-hole E (task x_async)) l) F ...) FS_1 ...))

        (where/error (tag x_label) v_coro)
        (where/error (ptr x_async) (malloc σ_0))
        (where/error σ_1 (ext1 σ_0 (x_async (new-task v_coro))))
        (where/error Q_1 (q-push Q_0 (frame (resume! v_coro (void)) x_async)))
        (where/error t_1 (step t_0))
        "spawn"]

   
   [--> (t_0 σ_0 Q_0 (FS_0 ... (stack (frame (in-hole E (run v)) l) F ...) FS_1 ...))
        (t_1 σ_1 Q_1 (FS_0 ... (stack (frame (in-hole E (task x_async)) l) F ...) FS_1 ...))

        (where/error (lambda () e) v)
        (where (ptr x_async) (malloc σ_0))
        (where σ_1 (ext1 σ_0 (x_async (new-task))))
        (where Q_1 (q-push Q_0 (frame e x_async)))
        (where t_1 (step t_0))
        "task-run"]

   ;; task awaiting

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame
                                     (in-hole E (tagged x_running (in-hole E_inner (await (task x_async))))) l)
                                    F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame (in-hole E (tag x_running)) l) F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (side-condition (not (term (in-tag? E_inner))))
        (where pending (task-status (lookup σ_0 x_async)))        
        (where x_dummy (gensym σ_0 dummy))
        (where v_coro
               (coroutine
                (lambda (x_dummy)
                  (in-hole E_inner (begin x_dummy
                                          (await (task x_async)))))))
        (where σ_1 (ext1 σ_0 (x_running v_coro)))
        (where t_1 (step t_0))
        "await-task-pending"]

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame (in-hole E (await (task x_async))) l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame (in-hole E v) l) F ...) FS_1 ...))

        (where/error v_obj (lookup σ_0 x_async))
        (where (done v) (task-status v_obj))
        (where σ_1 (ext1 σ_0 (x_async (task-awaited v_obj))))
        (where t_1 (step t_0))
        "task-await-done"]

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame (in-hole E (await (task x_async))) l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame (in-hole E (throw v)) l) F ...) FS_1 ...))

        (where/error v_obj (lookup σ_0 x_async))
        (where (failed v) (task-status v_obj))
        (where σ_1 (ext1 σ_0 (x_async (task-awaited v_obj))))
        (where t_1 (step t_0))
        "task-await-failed"]

   ;; Task finishing/rescheduling

   [--> (t_0 σ Q_0 (FS_0 ... (stack (frame v_coro l) F ...) FS_1 ...))
        (t_1 σ Q_1 (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where x_async l)
        (where v_obj (lookup σ x_async))
        (side-condition (term (task-coro-eq? v_obj v_coro)))
        (side-condition (not (term (task-cancelled? v_obj))))
        (where Q_1 (q-push Q_0 (frame (resume! v_coro (void)) l)))
        (where t_1 (step t_0))
        "task-reschedule"]

   [--> (t_0 σ_0 Q_0 (FS_0 ... (stack (frame v_coro l) F ...) FS_1 ...))
        (t_1 σ_1 Q_1 (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where x_async l)
        (where v_obj (lookup σ_0 x_async))
        (side-condition (term (task-coro-eq? v_obj v_coro)))
        (side-condition (term (task-cancelled? v_obj)))
        (where σ_1 (ext1 σ_0 (x_async (task-uncancel v_obj))))
        (where Q_1 (q-push Q_0 (frame (throw-in! v_coro "cancelled!") l)))
        (where t_1 (step t_0))
        "task-reschedule-cancelled"]

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame v l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where x_async l)
        (where/error v_obj (lookup σ_0 x_async))
        (side-condition (not (term (task-coro-eq? v_obj v))))
        (where σ_1 (ext1 σ_0 (x_async (task-settle v_obj v))))
        (where t_1 (step t_0))
        "task-return"]

   ;; stop task

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame (in-hole E (throw v)) l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (side-condition (not (term (in-handler?/aio E))))
        (where x_async l)
        (where/error v_obj (lookup σ_0 x_async))
        (where σ_1 (ext1 σ_0 (x_async (task-fail v_obj v))))
        (where t_1 (step t_0))
        "async-throw"]

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame (in-hole E (cancel (task x_async))) l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame (in-hole E (void)) l) F ...) FS_1 ...))

        (where v_obj (lookup σ_0 x_async))
        (where σ_1 (ext1 σ_0 (x_async (task-cancel v_obj))))
        (where t_1 (step t_0))
        "cancel"]

   ;; --------------------
   ;; OmniScient IO
   ;; --------------------
   
   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame (in-hole E (os/io natural v)) l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame (in-hole E (spawn (tag x_tag))) l) F ...) FS_1 ...))
        
        (where (x_dummy x_tag) (gensyms σ_0 σ_0))
        (where σ_1 (ext1 σ_0 (x_tag (coroutine (lambda (x_dummy)
                                                 (begin x_dummy
                                                        (while (<= (os/time) (+ t_0 natural))
                                                               (yield (tag x_tag)))
                                                        v))))) )
        (where/error t_1 (step t_0))
        "os/io"]

   [--> (t_0 σ Q (FS_0 ... (stack (frame (in-hole E (os/time)) l) F ...) FS_1 ...))
        (t_1 σ Q (FS_0 ... (stack (frame (in-hole E t_0) l) F ...) FS_1 ...))
        
        (where/error t_1 (step t_0))
        "os/time"]

   ;; --------------------
   ;; Platform exit
   ;; --------------------

   [--> (t_0 σ Q_0 (FS_main FS_0 ... (stack) FS_1 ...))
        (t_1 σ Q_1 (FS_main FS_0 ... (stack F_head) FS_1 ...))

        (where (F_head Q_1) (q-pop Q_0))
        (side-condition (term (all-busy? FS_0 ...)))
        (where t_1 (step t_0))
        "thread-work-steal"]
   
   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame e_0 l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame e_1 l) F ...) FS_1 ...))

        (side-condition (not (term (value? e))))
        (where (σ_1 e_1) (⇓base σ_0 e_0))
        (where t_1 (step t_0))
        "base-step"]
   
   [--> (t_0 σ Q ((stack (frame (in-hole E (block (tag x_coro))) l)) FS_1 ...))
        (t_1 σ Q ((stack (frame (in-hole E (block (resume! (tag x_coro) (void)))) l)) FS_1 ...))

        (where/error sync l)
        (where t_1 (step t_0))
        "block"]

   ;; The runtime can exit if all tasks have been awaited and threads aren't busy

   [--> (t_0 σ Q ((stack (frame (in-hole E (block v)) l)) FS_rest ...))
        (t_1 σ Q ((stack (frame (in-hole E v) l)) FS_rest ...))

        (where/error sync l)
        (side-condition (not (tag? (term v))))
        (side-condition (not (term (any-busy? FS_rest ...))))
        (where none (find-unawaited-error σ))
        (where t_1 (step t_0))
        "unblock"]

   [--> (t_0 σ Q ((stack (frame (in-hole E (block v)) l)) FS_rest ...))
        (t_1 σ Q ((stack (frame (in-hole E (throw v_error)) l)) FS_rest ...))

        (where/error sync l)
        (side-condition (not (tag? (term v))))
        (side-condition (not (term (any-busy? FS_rest ...))))
        (where v_error (find-unawaited-error σ))
        (where t_1 (step t_0))
        "unblock-throw"]))

;; -----------------------------------------------------------------------------
;; Metafunctions
;; -----------------------------------------------------------------------------

(define-metafunction AsyncIO
  new-task : v ... -> v
  [(new-task) (struct [running (kont)])]
  [(new-task v_inner)
   (struct
     [status "running"]
     [awaited #false]
     [cancelled #false]
     [value (void)]
     [inner v_inner])])

(define-metafunction AsyncIO
  task-coro : v -> v
  [(task-coro (struct _ ... [inner v_coro] _ ...)) v_coro]
  [(task-coro _) none])

(define-metafunction AsyncIO
  task-status : v -> (done v) or (failed v) or pending
  [(task-status (struct _ ... [status "done"] _ ... [value v] _ ...))
   (done v)]
  [(task-status (struct _ ... [status "failed"] _ ... [value v] _ ...))
   (failed v)]
  [(task-status (struct _ ... [status "running"] _ ...))
   pending])

(define-metafunction AsyncIO
  task-settle : v v -> v
  [(task-settle (struct
                  [x_0 v_0] ...
                  [status "running"]
                  [x_1 v_1] ...
                  [value _]
                  [x_2 v_2] ...) v)
   (struct
    [x_0 v_0] ...
    [status "done"]
    [x_1 v_1] ...
    [value v]
    [x_2 v_2] ...)])

(define-metafunction AsyncIO
  task-fail : v v -> v
  [(task-fail (struct
                [x_0 v_0] ...
                [status "running"]
                [x_1 v_1] ...
                [value _]
                [x_2 v_2] ...) v)
   (struct
     [x_0 v_0] ...
     [status "failed"]
     [x_1 v_1] ...
     [value v]
     [x_2 v_2] ...)])

(define-metafunction AsyncIO
  task-awaited : v -> v
  [(task-awaited (struct [x_0 v_0] ... [awaited _] [x_s v_s] ...))
   (struct [x_0 v_0] ... [awaited #true] [x_s v_s] ...)])

(define-metafunction AsyncIO
  task-coro-eq? : v v -> boolean
  [(task-coro-eq? v_struct v_coro) #true
                                   (where v_real (task-coro v_struct))
                                   (side-condition (equal? (term v_real) (term v_coro)))]
  [(task-coro-eq? _ _) #false])

(define-metafunction AsyncIO
  task-cancel : v -> v
  [(task-cancel (struct [x_0 v_0] ... [cancelled _] [x_s v_s] ...))
   (struct [x_0 v_0] ... [cancelled #true] [x_s v_s] ...)])

(define-metafunction AsyncIO
  task-uncancel : v -> v
  [(task-uncancel (struct [x_0 v_0] ... [cancelled _] [x_s v_s] ...))
   (struct [x_0 v_0] ... [cancelled #false] [x_s v_s] ...)]
  [(task-uncancel v) v])

(define-metafunction AsyncIO
  task-cancelled? : v -> boolean
  [(task-cancelled? (struct _ ... [cancelled boolean] _ ...))
   boolean])

(define-metafunction AsyncIO
  find-unawaited-error : σ -> v or none
  [(find-unawaited-error ((x_0 v_0) ...
                          (x (struct _ ...
                               [status "failed"] _ ...
                               [awaited #false] _ ...
                               [value v] _ ...)) (x_1 v_1) ...))
   v]
  [(find-unawaited-error _) none])

(define-metafunction/extension in-handler? AsyncIO
  in-handler?/aio : E -> boolean)

(define-metafunction AsyncIO
  value? : any -> boolean
  [(value? v) #true]
  [(value? any) #false])

(define-big-step ⇓base
  -->base AsyncIO)

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require "utils.rkt")

  (define-metafunction AsyncIO
    main/aio : e -> (t σ Q P)
    [(main/aio e) (0 () () ((stack (frame (substitute e) sync))
                            (stack)
                            #;(stack)))])

  (define (final-value p)
    (match p
      [`(,_t ,_H ,_Q ((stack (frame ,v sync)) ,_ ...)) v]
      [_ p]))
  
  (define (prog/equiv p v)
    ((default-equiv)
     (final-value p)
     v))
  
  (define-syntax-rule (aio-->>= e v)
    (test-->> -->aio #:equiv prog/equiv (term (main/aio e)) v))

  (define-syntax-rule (aio-->>∈ e results)
    (evaluates-in-set -->aio (term (main/aio e)) results
                      #:extract-result final-value))

  (aio-->>=
   (resume! ((async/lambda (x) 42) 0) (void))
   42)
  
  (aio-->>= 
   (trace-stdout (print)
                 (let* ([suspend (async/lambda () (void))]
                        [work (async/lambda (msg)
                                (begin (await (suspend))
                                       (print msg)))]
                        [c (work "A")])
                   (block c)))
   "A")

  (aio-->>= 
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))])
     (block (work)))
   42)

  (aio-->>= 
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))]
          [main (async/lambda () (await (spawn (work))))])
     (block (main)))
   42)

  (aio-->>= 
   (let* ([exn (async/lambda ()
                 (throw "whoops"))]
          [main (async/lambda ()
                  (begin (spawn (exn))
                         (await (os/io 5 42))))])
     (catch (lambda (e) e)
            (block (main))))
   "whoops")

  (aio-->>=
   (trace-stdout (print)
                 (let* ([append-it (async/lambda () (print "A"))]
                        [transparent (async/lambda ()
                                       (let ([ret (append-it)])
                                         (begin (print "B") ret)))])
                   (block (transparent))))
   "BA")

  (aio-->>∈
   (let* ([work (async/lambda ()
                  (catch (lambda (e) 42)
                         (await (os/io 4 0))))]
          [t (spawn (work))]
          [main (async/lambda ()
                  (begin (cancel t)
                         (await t)))])
     (block (main)))
   '(42 0))

  (aio-->>= 
   (trace-stdout (print)
                 (let* ([work (async/lambda (msg)
                                (print (await (os/io 1 msg))))]
                        [main (async/lambda ()
                                (let ([t1 (work "A")]
                                      [t2 (work "B")])
                                  (begin (print "C")
                                         (await t1)
                                         (await t2))))])
                   (block (main))))
   "CAB")

  (aio-->>∈ 
   (trace-stdout (print)
                 (let* ([work (async/lambda (msg)
                                (print (await (os/io 1 msg))))]
                        [main (async/lambda ()
                                (let ([t1 (work "A")]
                                      [t2 (spawn (work "B"))])
                                  (begin (print "C")
                                         (await t1)
                                         (await t2))))])
                   (block (main))))
   ; 'C' must *always* come before 'A'
   (filter (lambda (s) (before s #\C #\A))
           (string-permutations "ABC"))))