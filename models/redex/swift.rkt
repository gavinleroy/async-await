#lang racket

(require redex
         "lc.rkt"
         (prefix-in lib: (submod "lc.rkt" niceties))
         "lc+exn.rkt"
         "platform.rkt")

(define-extended-language Swift/Core LC+Exn
  (e ::= ....
     (async/lambda (x_!_ ...) e)
     (await e)
     (cancelled?))
  
  (v ::= ....
     (async/lambda (x_!_ ...) e)
     (task x_async))
  
  (E ::= ....
     (await E)
     (run E))

  #:binding-forms
  
  (async/lambda (x ...) e #:refers-to (shadow x ...)))

(define-event-loop
  Swift Swift/Core)

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->swift
  (reduction-relation
   Swift
   #:domain (t σ Q P)

   [--> (t_0 σ_0 Q_0 (FS_0 ... (stack (frame (in-hole E ((async/lambda (x ..._1) e) v ..._1)) l) F ...) FS_1 ...))
        (t_1 σ_1 Q_1 (FS_0 ... (stack (frame (in-hole E (task x_async)) l) F ...) FS_1 ...))
        
        (where (ptr x_async) (malloc σ_0))
        (where/error σ_1 (ext σ_0 (x_async (new-task (task-owner l))) (x v) ...))
        (where/error Q_1 (q-push Q_0 (frame e x_async)))
        (where/error t_1 (step t_0))
        "async-app"]

   [--> (t_0 σ_0 Q (FS_0 ... (stack (name parent-frame (frame v l)) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack F ...) FS_1 ...))
        
        (side-condition (async? (term l)))
        (where x_async l)
        (where (some x_child) (task-tree-running-child σ_0 x_async))
        (where/error σ_1 (ext1 (x_child (task-push-waiting (lookup σ_0 x_child) parent-frame))))
        (where/error t_1 (step t_0))
        "task-return-await-children"]

   [--> (t_0 σ_0 Q_0 (FS_0 ... (stack (frame v l) F ...) FS_1 ...))
        (t_1 σ_1 Q_1 (FS_0 ... (stack F ...) FS_1 ...))
        
        (side-condition (async? (term l)))
        (where x_async l)
        (where none (task-tree-running-child σ_0 x_async))
        (where/error v_obj (lookup σ_0 x_async))
        (where/error (pending F_waiting ...) (task-status v_obj))
        (where/error σ_1 (ext1 σ_0 (x_async (task-settle v_obj v))))
        (where/error Q_1 (q-push Q_0 F_waiting ...))
        (where/error t_1 (step t_0))
        "task-return"]

   [--> (t_0 σ Q (FS_0 ... (stack (frame (in-hole E (await (task x_async))) l) F ...) FS_1 ...))
        (t_1 σ Q (FS_0 ... (stack (frame (in-hole E v) l) F ...) FS_1 ...))

        (where (done v) (task-status (lookup σ x_async)))
        (where/error t_1 (step t_0))
        "await-continue"]

   [--> (t_0 σ Q (FS_0 ... (stack (frame (in-hole E (await (task x_async))) l) F ...) FS_1 ...))
        (t_1 σ Q (FS_0 ... (stack (frame (in-hole E (throw v)) l) F ...) FS_1 ...))

        (where (failed v) (task-status (lookup σ x_async)))
        (where/error t_1 (step t_0))
        "await-failed"]

   [--> (t_0 σ_0 Q (FS_0 ... (stack (name current-frame
                                          (frame (in-hole E (await (task x_async))) l)) F ...)
                    FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where v_obj (lookup σ_0 x_async))
        (where (pending _ ...) (task-status v_obj))
        (where/error σ_1 (ext1 σ_0 (x_async (task-push-waiting v_obj current-frame))))
        (where/error t_1 (step t_0))
        "await"]

   [--> (t_0 σ_0 Q_0 (FS_0 ... (stack (frame (in-hole E (throw v_err)) l) F ...) FS_1 ...))
        (t_1 σ_1 Q_1 (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (side-condition (not (term (in-handler?/swift E))))
        (where x_async l)
        (where v_obj (lookup σ_0 x_async))
        (where/error (pending F_waiting ...) (task-status v_obj))
        (where/error σ_1 (ext1 σ_0 (x_async (task-fail v_obj v_err))))
        (where/error Q_1 (q-push Q_0 F_waiting ...))
        (where/error t_1 (step t_0))
        "async-throw"]

   [--> (t_0 σ Q (FS_0 ... (stack (frame (in-hole E (cancelled?)) l) F ...) FS_1 ...))
        (t_1 σ Q (FS_0 ... (stack (frame (in-hole E is-cancelled?) l) F ...) FS_1 ...))

        (side-condition (async? (term l)))
        (where x_async l)
        (where is-cancelled? (task-ancestor-cancelled? σ_0 x_async))
        (where/error t_1 (step t_0))
        "cancelled?"]

   ;; --------------------
   ;; OmniScient IO, OS/IO
   ;; --------------------

   ;; TODO, is cancelled check
   [--> (t_0 σ_0 Q_0 (FS_0 ... (stack (frame (in-hole E (os/io natural v)) l) F ...) FS_1 ...))
        (t_1 σ_1 Q_1
             (FS_0 ... (stack (frame (in-hole E (task x_async)) l) F ...) FS_1 ...))

        (where (ptr x_async) (malloc σ_0))
        (where σ_1 (ext1 σ_0 (x_async (new-task))))
        (where Q_1 (q-push Q_0 (frame (os/resolve (task x_async) (lib:Σ t_0 natural) v) x_async)))
        (where t_1 (step t_0))
        "os/io"]
   
   [--> (t_0 σ_0 Q_0
             (FS_0 ... (stack (frame (in-hole E (os/resolve (task x_async) t_resolve v)) l) F ...)
                   FS_1 ...))
        (t_1 σ_1 Q_1 (FS_0 ... (stack F ...) FS_1 ...))

        (side-condition (>= (term t_0) (term t_resolve)))
        (where v_obj (lookup σ_0 x_async))
        (where/error (pending F_waiting ...) (task-status v_obj))
        (where/error σ_1 (ext1 σ_0 (x_async (task-settle v_obj v))))
        (where/error Q_1 (q-push Q_0 F_waiting ...))
        (where/error t_1 (step t_0))
        "os/resolve"]

   [--> (t_0 σ Q (FS_0 ... (stack (frame (in-hole E (os/resolve v_task t_resolve v)) l) F ...) FS_1 ...))
        (t_1 σ Q (FS_0 ... (stack (frame (in-hole E (os/resolve v_task t_resolve v)) l) F ...) FS_1 ...))

        (side-condition (< (term t_0) (term t_resolve)))
        (where/error t_1 (step t_0))
        "os/resolve-blocking"]

   
   [--> (t_0 σ Q_0 (FS_main FS_0 ... (stack) FS_1 ...))
        (t_1 σ Q_1 (FS_main FS_0 ... (stack F_head) FS_1 ...))

        (side-condition (term (all-busy? FS_0 ...)))
        (where (F_head Q_1) (q-pop Q_0))
        (where t_1 (step t_0))
        "thread-work-steal"]

   [--> (t_0 σ_0 Q (FS_0 ... (stack (frame e_0 l) F ...) FS_1 ...))
        (t_1 σ_1 Q (FS_0 ... (stack (frame e_1 l) F ...) FS_1 ...))

        (side-condition (not (term (value? e))))
        (where (σ_1 e_1) (⇓base σ_0 e_0))
        (where t_1 (step t_0))
        "base-step"]

   ;; --------------------
   ;; Platform exit
   ;; --------------------

   ;; TODO, Swift exit conditions
   [--> (t_0 σ Q ((stack (frame (in-hole E (block (task x_async))) l)) FS_rest ...))
        (t_1 σ Q ((stack (frame (in-hole E v) l)) FS_rest ...))

        (side-condition (sync? (term l)))
        (where (done v) (task-status (lookup σ x_async)))
        (where/error t_1 (step t_0))
        "unblock"]))

(define -->base
  (extend-reduction-relation -->exn Swift))

;; -----------------------------------------------------------------------------
;; Metafunctions
;; -----------------------------------------------------------------------------

(define-big-step ⇓base
  -->base Swift)

(define-metafunction/extension in-handler? Swift
  in-handler?/swift : E -> boolean)

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "lc.rkt" niceties)
           "utils.rkt")
  
  (define-syntax-rule (swift-->>= e v)
    (test-->> -->swift #:equiv prog/equiv (async/main #:threads 2 e) v))

  (define-syntax-rule (swift-->>∈ e results)
    (evaluates-in-set -->swift (async/main #:threads 2 e) results
                      #:extract-result program-output))
  
  (swift-->>=
   (block ((async/lambda () 42)))
   42)

  (swift-->>=
   (block ((async/lambda (x) x) 42))
   42)

  (swift-->>=
   (let* ([yield (async/lambda () (void))]
          [id (async/lambda (x)
                (begin
                  (await (yield))
                  x))])
     
     (block (id 42)))
   42)

  (swift-->>=
   (let* ([mk-t1 (async/lambda () (throw 42))]
          [mk-t2 (async/lambda (x)
                   (catch (lambda (v) v)
                          (begin
                            (await (mk-t1))
                            x)))])
     
     (block (mk-t2 0)))
   42)

  (swift-->>=
   (let ([work (async/lambda () (await (os/io 5 42)))])
     (block (work)))
   42)

  (swift-->>=
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (begin
                      (print (await (os/io 1 msg)))
                      (print (await (os/io 1 msg)))))])
       (block (work "A"))))
   "AA")

  (swift-->>∈
   (trace-stdout (print)
     (let* ([get-truth (async/lambda () #true)]
            [work (async/lambda (msg)
                    (dotimes (i 3)
                             (when (await (get-truth))
                               (print msg))))]
            [main (async/lambda ()
                    (let ([task0 (work "A")]
                          [task1 (work "B")])
                      (begin (print "C")
                             (await task0)
                             (await task1))))])
       (block (main))))
   (map (lambda (s) (string-append "C" s))
        (string-permutations "AAABBB")))

  (swift-->>∈
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (begin (await (os/io 5 (void)))
                           (print msg)))]
            [main (async/lambda ()
                    (let ([task0 (work "A")]
                          [task1 (work "B")])
                      (begin (print "C")
                             (await task0)
                             (await task1))))])
       (block (main))))
   (string-permutations "ABC")))