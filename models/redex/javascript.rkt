#lang racket

(require redex
         "lc.rkt"
         "lc+exn.rkt"
         "platform.rkt")

;; TODO: because promises are a user-space construct,
;; should the JS semantics just use structs and callbacks?
;; Or is this fine as modeled?

(define-extended-language JS/Core LC+Exn
  (e ::= ....
     (async/lambda (x_!_ ...) e)
     (await e))

  (v ::= ....
     (async/lambda (x_!_ ...) e)
     (task x_async))

  (E ::= ....
     (await E))

  #:binding-forms

  (async/lambda (x ...) e #:refers-to (shadow x ...)))

(define-event-loop
  JS JS/Core)

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->js
  (reduction-relation
   JS
   #:domain (t σ Q P)

   [--> (t_0 σ_0 Q ((stack (frame (in-hole E ((async/lambda (x ..._1) e) v ..._1)) l) F ...)))
        (t_1 σ_1 Q ((stack (frame e x_async) (frame (in-hole E (task x_async)) l) F ...)))
        
        (where (ptr x_async) (malloc σ_0))
        (where σ_1 (ext σ_0 (x_async (struct [running (kont)])) (x v) ...))
        (where t_1 (step t_0))
        "async-app"]

   [--> (t_0 σ_0 Q_0 ((stack (frame v l) F ...)))
        (t_1 σ_1 Q_1 ((stack F ...)))

        (side-condition (async? (term l)))
        (where x_async l)
        (where/error (struct [running (kont F_waiting ...)]) (lookup σ_0 x_async))
        (where σ_1 (ext1 σ_0 (x_async (struct [done v]))))
        (where Q_1 (q-push Q_0 F_waiting ...))
        (where t_1 (step t_0))
        "task-return"]

   [--> (t_0 σ Q_0 ((stack (frame (in-hole E (await (task x_async))) l) F ...)))
        (t_1 σ Q_1 ((stack F ...)))

        (where (struct [done v]) (lookup σ x_async))
        (where Q_1 (q-push Q_0 (frame (in-hole E v) l)))
        (where t_1 (step t_0))
        "await-continue"]

   [--> (t_0 σ Q_0 ((stack (frame (in-hole E (await (task x_async))) l) F ...)))
        (t_1 σ Q_1 ((stack F ...)))

        (where (struct [failed v]) (lookup σ x_async))
        (where Q_1 (q-push Q_0 (frame (in-hole E (throw v)) l)))
        (where t_1 (step t_0))
        "await-failed"]

   [--> (t_0 σ_0 Q ((stack (name current-frame
                                 (frame (in-hole E (await (task x_async))) l)) F ...)))
        (t_1 σ_1 Q ((stack F ...)))

        (side-condition (async? (term l)))
        (where (struct [running (kont F_waiting ...)]) (lookup σ_0 x_async))
        (where σ_1 (ext1 σ_0 (x_async (struct [running (kont current-frame F_waiting ...)]))))
        (where t_1 (step t_0))
        "await"]

   [--> (t_0 σ_0 Q_0 ((stack (frame (in-hole E (throw v_err)) l) F ...)))
        (t_1 σ_1 Q_1 ((stack F ...)))

        (side-condition (async? (term l)))
        (side-condition (not (term (in-handler?/js E))))
        (where x_async l)
        (where/error (struct [running (kont F_waiting ...)]) (lookup σ_0 x_async))
        (where σ_1 (ext1 σ_0 (x_async (struct [failed v_err]))))
        (where Q_1 (q-push Q_0 F_waiting ...))
        (where t_1 (step t_0))
        "async-throw"]

   ;; --------------------
   ;; OmniScient IO, OS/IO
   ;; --------------------

   [--> (t_0 σ_0 Q_0 ((stack (frame (in-hole E (os/io natural v)) l) F ...)))
        (t_1 σ_1 Q_1 ((stack (frame (in-hole E (task x_async)) l) F ...)))

        (where (ptr x_async) (malloc σ_0))
        (where σ_1 (ext1 σ_0 (x_async (struct [running (kont)]))))
        (where Q_1 (q-push Q_0 (frame (os/resolve (task x_async) (Σ t_0 natural) v) x_async)))
        (where t_1 (step t_0))
        "os/io"]

   [--> (t_0 σ_0 Q_0 ((stack (frame (in-hole E (os/resolve (task x_async) t_resolve v)) l) F ...)))
        (t_1 σ_1 Q_1 ((stack F ...)))

        (side-condition (>= (term t_0) (term t_resolve)))
        (where/error (struct [running (kont F_waiting ...)]) (lookup σ_0 x_async))
        (where σ_1 (ext1 σ_0 (x_async (struct [done v]))))
        (where Q_1 (q-push Q_0 F_waiting ...))
        (where t_1 (step t_0))
        "os/resolve"]

   [--> (t_0 σ Q_0 ((stack (name current-frame
                                 (frame (in-hole E (os/resolve v_task t_resolve v)) l)) F ...)))
        (t_1 σ Q_1 ((stack F ...)))

        (side-condition (< (term t_0) (term t_resolve)))
        (where Q_1 (q-push Q_0 current-frame))
        (where t_1 (step t_0))
        "os/resolve-blocking"]


   [--> (t_0 σ Q_0 ((stack)))
        (t_1 σ Q_1 ((stack F_head)))

        (where (F_head Q_1) (q-pop Q_0))
        (where t_1 (step t_0))
        "thread-work-steal"]

   [--> (t_0 σ_0 Q ((stack (frame e_0 l) F ...)))
        (t_1 σ_1 Q ((stack (frame e_1 l) F ...)))

        (side-condition (not (term (value? e))))
        (where (σ_1 e_1) (⇓base σ_0 e_0))
        (where t_1 (step t_0))
        "base-step"]

   ;; --------------------
   ;; Platform exit
   ;; --------------------

   [--> (t_0 σ Q_0 ((stack (name current-frame
                                 (frame (in-hole E (block (task x_async))) l)))))
        (t_1 σ Q_1 ((stack)))

        (side-condition (sync? (term l)))
        (where (struct [running (kont F_waiting ...)]) (lookup σ x_async))
        (where Q_1 (q-push Q_0 current-frame))
        (where t_1 (step t_0))
        "block"]
   
   ;; TODO, JS exit conditions
   [--> (t_0 σ Q ((stack (frame (in-hole E (block (task x_async))) l))))
        (t_1 σ Q ((stack (frame (in-hole E v) l))))

        (side-condition (sync? (term l)))
        (where (struct [done v]) (lookup σ x_async))
        (where t_1 (step t_0))
        "unblock"]))

(define -->base
  (extend-reduction-relation -->exn JS))

;; -----------------------------------------------------------------------------
;; Metafunctions
;; -----------------------------------------------------------------------------

(define-big-step ⇓base
  -->base JS)

(define-metafunction/extension in-handler? JS
  in-handler?/js : E -> boolean)

(define-metafunction JS
  value? : any -> boolean
  [(value? v) #true]
  [(value? any) #false])

(define-metafunction JS
  task? : v -> boolean
  [(task? (task _)) #true]
  [(task? _) #false])

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require "utils.rkt")

  (define-metafunction JS
    main/js : e -> (t σ Q P)
    [(main/js e) (0 () () ((stack (frame (substitute e) sync))))])

  (define (final-value p)
    (match p
      [`(,_t ,_σ ,_Q ((stack (frame ,v sync)))) v]
      [_ p]))

  (define (prog/equiv p v)
    ((default-equiv)
     (final-value p)
     v))

  (define-syntax-rule (js-->>= e v)
    (test-->> -->js #:equiv prog/equiv (term (main/js e)) v))

  (define-syntax-rule (js-->>∈ e results)
    (evaluates-in-set -->js (term (main/js e)) results
                      #:extract-result final-value))

  (js-->>=
   (block ((async/lambda () 42)))
   42)

  (js-->>=
   (block ((async/lambda (x) x) 42))
   42)

  (js-->>=
   (let* ([yield (async/lambda () (void))]
          [id (async/lambda (x)
                (begin
                  (await (yield))
                  x))])

     (block (id 42)))
   42)

  (js-->>=
   (let* ([mk-t1 (async/lambda () (throw 42))]
          [mk-t2 (async/lambda (x)
                   (catch (lambda (v) v)
                          (begin
                            (await (mk-t1))
                            x)))])

     (block (mk-t2 0)))
   42)

  (js-->>=
   (let ([work (async/lambda () (await (os/io 5 42)))])
     (block (work)))
   42)

  (js-->>=
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (begin
                      (print (await (os/io 1 msg)))
                      (print (await (os/io 1 msg)))))])
       (block (work "A"))))
   "AA")

  (js-->>=
   (trace-stdout (print)
     (let* ([get-truth (async/lambda () #true)]
            [work (async/lambda (msg)
                    (begin (print msg)
                           (dotimes (_ 3)
                                    (when (await (get-truth))
                                      (print msg)))))]
            [main (async/lambda ()
                    (let ([task0 (work "A")]
                          [task1 (work "B")])
                      (begin (print "C")
                             (await task0)
                             (await task1))))])
       (block (main))))
   "ABCABABAB")

  (js-->>=
   (trace-stdout (print)
     (let* ([get-truth (async/lambda () (throw "T"))]
            [work (async/lambda (msg)
                    (begin (print msg)
                           (dotimes (_ 3)
                                    (when (await (get-truth))
                                      (print msg)))))]
            [main (async/lambda ()
                    (let ([task0 (work "A")]
                          [task1 (work "B")])
                      (catch (lambda (e) (print e))
                             (begin (print "C")
                                    (await task0)
                                    (await task1)))))])
       (block (main))))
   "ABCT")
  
  (js-->>=
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
   "CAB"))
