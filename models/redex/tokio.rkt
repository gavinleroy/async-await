#lang racket

(require redex
         "lc.rkt"
         (prefix-in lib: (submod "lc.rkt" niceties))
         "lc+exn.rkt"
         "lc+coro.rkt"
         "rust.rkt"
         "platform.rkt")

(define-extended-language Tokio/Core Rust

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
  Tokio Tokio/Core)

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->base
  (extend-reduction-relation -->rs Tokio))

(define -->tokio
  (reduction-relation
   Tokio #:domain (t σ Q P)

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
        (where/error σ_1 (ext1 σ_0 (x_async (new-task))))
        (where/error Q_1 (q-push Q_0 (frame e x_async)))
        (where/error t_1 (step t_0))
        "task-run"]

   ;; task awaiting

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame
                                     (in-hole E (tagged x_running (in-hole E_inner (await (task x_async))))) l)
                                    F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame (in-hole E (tag x_running)) l) F ...) FS_1 ...))

        (side-condition (not (term (in-tag? E_inner))))
        (side-condition (not (term (task-ready? (lookup σ_0 x_async)))))        
        (where/error x_dummy (gensym σ_0 dummy))
        (where/error v_coro
                     (coroutine
                      (lambda (x_dummy)
                        (in-hole E_inner (lib:begin x_dummy
                                                (await (task x_async)))))))
        (where/error σ_1 (ext1 σ_0 (x_running v_coro)))
        (where/error t_1 (step t_0))
        "await-task-pending"]
   
   [--> (t_0 σ Q (FS_0 ... (stack (frame (in-hole E (await (task x_async))) l) F ...) FS_1 ...))
        (t_1 σ Q (FS_0 ... (stack (frame (in-hole E v) l) F ...) FS_1 ...))

        (where/error v_obj (lookup σ x_async))
        (where (done v) (task-status v_obj))
        (where/error t_1 (step t_0))
        "task-await-done"]

   [--> (t_0 σ Q (FS_0 ... (stack (frame (in-hole E (await (task x_async))) l) F ...) FS_1 ...))
        (t_1 σ Q (FS_0 ... (stack (frame (in-hole E (struct)) l) F ...) FS_1 ...))

        (where v_obj (lookup σ x_async))
        (where cancelled (task-status v_obj))
        (where/error t_1 (step t_0))
        "task-await-cancelled"]

   ;; Task finishing/rescheduling

   [--> (t_0 σ Q_0 (FS_0 ... (stack (frame v_coro l) F ...) FS_1 ...))
        (t_1 σ Q_1 (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where x_async l)
        (where v_obj (lookup σ x_async))
        (side-condition (term (task-coro-eq? v_obj v_coro)))
        (where (pending _ ...) (task-status v_obj))
        (where/error Q_1 (q-push Q_0 (frame (resume! v_coro (void)) l)))
        (where/error t_1 (step t_0))
        "task-reschedule"]

   [--> (t_0 σ Q (FS_0 ... (stack (frame v_coro l) F ...) FS_1 ...))
        (t_1 σ Q (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where x_async l)
        (where v_obj (lookup σ x_async))
        (side-condition (term (task-coro-eq? v_obj v_coro)))
        (where cancelled (task-status v_obj))
        (where/error t_1 (step t_0))
        "task-reschedule-cancelled"]

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame v l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where x_async l)
        (where v_obj (lookup σ_0 x_async))
        (side-condition (not (term (task-coro-eq? v_obj v))))
        (where/error σ_1 (ext1 σ_0 (x_async (task-settle v_obj v))))
        (where/error t_1 (step t_0))
        "task-return"]

   ;; stop task

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame (in-hole E (cancel (task x_async))) l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame (in-hole E (void)) l) F ...) FS_1 ...))

        (where v_obj (lookup σ_0 x_async))
        (where/error σ_1 (ext1 σ_0 (x_async (task-cancel v_obj))))
        (where/error t_1 (step t_0))
        "cancel"]

   ;; --------------------
   ;; OmniScient IO
   ;; --------------------
   
   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame (in-hole E (os/io natural v)) l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame (in-hole E (spawn (tag x_tag))) l) F ...) FS_1 ...))
        
        (where (x_dummy x_tag) (lib:gensyms σ_0 σ_0))
        (where σ_1 (ext1 σ_0 (x_tag (coroutine (lambda (x_dummy)
                                                 (lib:begin x_dummy
                                                        (lib:while (<= (os/time) (lib:Σ t_0 natural))
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
        (t_1 σ Q ((stack (frame (in-hole E (block (spawn (tag x_coro)))) l)) FS_1 ...))

        (where/error sync l)
        (where/error t_1 (step t_0))
        "block"]

   [--> (t_0 σ Q ((stack (frame (in-hole E (block (task x_async))) l)) FS_rest ...))
        (t_1 σ Q ((stack (frame (in-hole E v) l)) FS_rest ...))

        (where/error sync l)
        (where (done v) (task-status (lookup σ x_async)))
        (where/error t_1 (step t_0))
        "unblock"]))

;; -----------------------------------------------------------------------------
;; Metafunctions
;; -----------------------------------------------------------------------------

(define-big-step ⇓base
  -->base Tokio)

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "lc.rkt" niceties)
           "utils.rkt")
  
  (define-syntax-rule (tokio-->>= e v)
    (test-->> -->tokio #:equiv prog/equiv (async/main #:threads 2 e) v))

  (define-syntax-rule (tokio-->>∈ e results)
    (evaluates-in-set -->tokio (async/main #:threads 1 e) results
                      #:extract-result program-output))

  (tokio-->>=
   (resume! ((async/lambda (x) 42) 0) (void))
   42)
  
  (tokio-->>= 
   (trace-stdout (print)
     (let* ([suspend (async/lambda () (void))]
            [work (async/lambda (msg)
                    (begin (await (suspend))
                           (print msg)))]
            [c (work "A")])
       (block c)))
   "A")
  
  (tokio-->>= 
   (let* ([work (async/lambda ()
                  (await (os/io 1 42)))])
     (block (work)))
   42)
  
  (tokio-->>= 
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))])
     (block (work)))
   42)

  (tokio-->>= 
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))]
          [main (async/lambda () (await (spawn (work))))])
     (block (main)))
   42)

  (tokio-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda () (print "A"))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (block (transparent))))
   "B")

  (tokio-->>∈
   (trace-stdout (print)
     (let* ([work (async/lambda ()
                    (while #true
                           (await (os/io 1 (print "A")))))]
            [t (spawn (work))]
            [main (async/lambda ()
                    (begin (await (os/io 2 (void)))
                           (cancel t)))])
       (block (main))))
   (for/list ([i (in-range 100)])
     (make-string i #\A)))

  (tokio-->>= 
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

  (tokio-->>∈ 
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