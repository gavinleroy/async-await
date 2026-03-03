#lang racket

(require (for-syntax racket/base syntax/parse)
         redex/reduction-semantics
         "core.rkt")

(provide (all-defined-out))

(struct nondeterministic exn:fail:user (prog results))

;; Reduce the `term` using `rule`.
;;
;; If `max-steps` is provided the reduction will be capped at that many times, otherwise, it could loop forever
;; If the reduction is `deterministic?` a form that reduces to multiple results is considered an error; a `nondeterministic` exception is thrown.
;; The function `α-equiv?` is used to filter programs that are alpha equivalent. By default syntactic equivalence `equal?` is used.
(define (reduce rule term
                #:deterministic? [det? #false]
                #:max-steps [max-steps #false]
                #:α-equiv? [α-equiv? equal?])
  (define iterator (if (real? max-steps)
                       (in-range max-steps)
                       (in-naturals)))
  (for/fold ([term term]
             [iterated? #false]
             #:result (and iterated? term))
            ([_ iterator]
             #:do [(define next-progs
                     (remove-duplicates (apply-reduction-relation rule term)
                                        α-equiv?))]
             #:break (empty? next-progs))
    (match next-progs
      [(list reduced) (values reduced #true)]
      [many
       (if det?
           (raise (nondeterministic term many))
           (values (car (shuffle many)) #true))])))

(struct in-set-evaluation exn:fail:user (prog result results))

;; A testing help that asserts, after each evaluation of `term` using the reduction relation `rule`, the value
;; extracted from the result using `extract` is tested for membership in results using `equiv?`. A maximum of
;; `iterations` iterations are performed.
(define (evaluates-in-set rule term results #:iterations [iters 50] #:extract-result extract #:equiv? [equiv? equal?])
  (for ([_ (in-range iters)])
    (define final (reduce rule term #:deterministic? #false))
    (define result (extract final))
    (unless (and result (member result results equiv?))
      (raise (in-set-evaluation term final results)))))

;; Inject symbols into the current scope attached to location `srcloc`
(begin-for-syntax
  (define-syntax-rule (with-unhygenic srcloc (name ...) body)
    (with-syntax ([name (datum->syntax srcloc 'name srcloc)] ...)
      body)))

;;;;
;; Main entry point

(define-syntax (define-extended-ev-system stx)
  (syntax-parse stx
    [(_ Lang:id
        #:def-reduction red/lang:id
        #:def-threaded-lang SysLang:id
        #:with-base-lang BaseLang:id
        #:with-base-reduction red/base
        (~optional (~seq #:halt-on-exn? exn?:boolean))
        grammar-rule:expr ...
        (~optional (~seq #:binding-forms bf:expr ...)))
     (with-syntax ([(⇓base ⇓sys) (generate-temporaries #'(red/base red/base))])
       (with-unhygenic #'Lang (
                               ;; STD
                               async/main
                               step

                               find-unawaited-error
                               value?
                               program-output
                               prog/equiv

                               Q:pop Q:push T:push T:pop

                               task:settled? ;; indented for meta code
                               task:allocate
                               task:create-new
                               task:set-done!
                               task:set-failed!
                               task:set-cancelled!
                               task:is-cancelled?
                               task:is-completed?
                               task:get-result
                               task:add-waiter!
                               task:get-waiters
                               )
         #'(begin
             ;; The systems language `SysLang` is the base lambda calculus, either LC or LC+Exn,
             ;; extended with a multithreaded platform. There are also the OmniScient hooks:
             ;; `os/time`, `os/io`, `os/start-soon`, and `os/start-later`.
             (define-extended-language SysLang BaseLang
               (e ::= ....
                  (os/time)                          ;; get the current time step
                  (os/io e_delay e)                  ;; perform an IO operation that takes (at least) `e_delay` time steps and returns `e`
                  (os/start-soon e)          ;; schedule the evaluation of `e` with the frame label `e_label`
                  (os/start-later e_time label e)) ;; schedule the signal of operation `e` at (at least) timestep `e_time` with the frame label `e_label`

               (E ::= ....
                  (os/io E e)
                  (os/io v E)
                  (os/start-soon E)
                  (os/start-later E label e)
                  (os/start-later v label E))

               ;; Timestep `t`
               (t ::= natural)

               ;; Frame label, `x` a task, or `'root`
               (label ::= x root)

               ;; The waiting queue, a queue of thunks to run with frame label `label`
               (Q ::= ((label (lambda (x) e)) (... ...)))

               ;; The signal queue, thunks to get rescheduled at time step `t`, with frame label `label`
               (T ::= ((t label (lambda (x) e)) (... ...)))

               ;; An executing frame, the expressions `e` evaluates with label `label`
               (F ::= (label e))

               ;; A thread, which holds a stack of evaluating frames `F ...`
               (FS ::= (thread F (... ...)))

               ;; A program, `FS ...` is a set of running threads
               (P ::= (FS (... ...))))

             (define-extended-language Lang SysLang
               grammar-rule ...
               (~? (~@ #:binding-forms bf ...)))

             ;; Given a reduction relation `red` and a `term`, evalaute the term many times
             ;; using the provided relation. If the term is `det?`, reducing to multiple
             ;; forms is considered an error, if not, a random reduction is chosen and continued with.
             ;;
             ;; We want to use non-deterministic reductions with the threaded model. The goal is *not*
             ;; to model fine-grained memory access, so we take larger steps as a regular system would.
             ;; Decisions are then made when as async/lambda or await form is reached in one of the threads.
             (define (big-step red term #:deterministic? [det? #true])
               (with-handlers ([nondeterministic? (lambda (e) 'stuck)])
                 (let* ([α-equiv? (lambda (a b) (alpha-equivalent? Lang a b))]
                        [reduced (reduce red term
                                         #:deterministic? det?
                                         #:max-steps 200
                                         #:α-equiv? α-equiv?)])
                   (when (α-equiv? term reduced)
                     (raise 'big-step "form reduced to itself"))
                   reduced)))

             ;; Provided a base program as `stx`, wrap that program in an evaluation context `P` using `thrds` threads.
             (define-syntax (async/main stx)
               (syntax-parse stx
                 [(_ (~optional (~seq #:threads thrds:integer)) e)
                  (define workers (for/list ([i (in-range 1 (syntax-e #'(~? thrds 1)))]) '(thread)))
                  #`(term-let ([(thrd (... (... ...))) '#,workers])
                              (term (#;t 0 #;σ () #;Q () #;T () #;PS ((thread (root e)) thrd (... (... ...))))
                                    #:lang Lang))]))

             (define -->sys/sync
               (extend-reduction-relation
                (extend-reduction-relation red/base SysLang) Lang))

             (define -->sys/threaded
               (reduction-relation
                Lang
                #:domain (t σ Q T P)

                [--> (t_0 σ_0 Q T (FS_0 (... ...) (thread (label e_0) F (... ...)) FS_1 (... ...)))
                     (t_1 σ_1 Q T (FS_0 (... ...) (thread (label e_1) F (... ...)) FS_1 (... ...)))

                     (side-condition (not (value? (term e_0))))
                     (where (σ_1 e_1) ,(big-step -->sys/sync (term (σ_0 e_0))))
                     (where/error t_1 (step t_0))
                     "base-lang/reduce"]

                [--> (t_0 σ Q T (FS_0 (... ...) (thread (label (in-hole E (os/time))) F (... ...)) FS_1 (... ...)))
                     (t_1 σ Q T (FS_0 (... ...) (thread (label (in-hole E t_0)) F (... ...)) FS_1 (... ...)))

                     (where/error t_1 (step t_0))
                     "os/time"]

                [--> (t_0 σ Q_0 T (FS_0 (... ...) (thread (label (in-hole E (os/start-soon (list (list (ptr label_waiting) v) (... ...))))) F (... ...)) FS_1 (... ...)))
                     (t_1 σ Q_1 T (FS_0 (... ...) (thread (label (in-hole E (void))) F (... ...)) FS_1 (... ...)))

                     (where/error Q_1 (Q:push Q_0 (label_waiting v) (... ...)))
                     (where/error t_1 (step t_0))
                     "os/start-soon"]

                [--> (t_0 σ Q T_0 (FS_0 (... ...) (thread (label (in-hole E (os/start-later t x v))) F (... ...)) FS_1 (... ...)))
                     (t_1 σ Q T_1 (FS_0 (... ...) (thread (label (in-hole E (void))) F (... ...)) FS_1 (... ...)))

                     (where/error T_1 (T:push T_0 (t x v)))
                     (where/error t_1 (step t_0))
                     "os/start-later"]

                ;; NOTE, the thread matching is to force thread evaluation from left to right
                [--> (t_0 σ Q_0 T ((thread F F_rs (... ...)) (... ...) (thread) FS_1 (... ...)))
                     (t_1 σ Q_1 T ((thread F F_rs (... ...)) (... ...) (thread (label_waiting (v_thunk (void)))) FS_1 (... ...)))

                     (where ((label_waiting v_thunk) Q_1) (Q:pop Q_0))
                     (where/error t_1 (step t_0))
                     "sys/schedule"]

                [--> (t σ Q T (FS_0 (... ...) (thread (label (void)) F_rs (... ...)) FS_1 (... ...)))
                     (t σ Q T (FS_0 (... ...) (thread F_rs (... ...)) FS_1 (... ...)))

                     (side-condition (not (eq? 'root (term label))))
                     "sys/thread-exit"]

                [--> (t_0 σ Q_0 T_0 P)
                     (t_1 σ Q_1 T_1 P)

                     (where ((label v) T_1) (T:pop t_0 T_0))
                     (where/error Q_1 (Q:push Q_0 (label v)))
                     (where/error t_1 (step t_0))
                     "sys/signal"]))

             (define -->sys/combined
               (reduction-relation
                Lang
                #:domain (t σ Q T P)

                [--> (t_0 σ_0 Q_0 T_0 P_0)
                     (t_1 σ_1 Q_1 T_1 P_1)

                     (where (t_1 σ_1 Q_1 T_1 P_1)
                            ,(big-step -->sys/threaded (term (t_0 σ_0 Q_0 T_0 P_0))
                                       #:deterministic? #false))
                     "sys-lang/reduce"]))

             (define red/lang -->sys/combined #;-->sys/threaded)

             ;;;;
             ;; Std Implementations

             (define (value? t)
               (redex-match? Lang v t))

             (define-metafunction Lang
               find-unawaited-error : σ -> (some v) or none
               [(find-unawaited-error (_ (... ...)
                                         (_ (struct _ (... ...)
                                              [status "failed"] _ (... ...)
                                              [awaited #false] _ (... ...)
                                              [value v] _ (... ...))) _ (... ...)))
                (some v)]
               [(find-unawaited-error _) none])

             (define (program-output p)
               (match p
                 [`(,_t ,_H ,_Q ,_T ((thread (root ,v)) ,_ (... ...))) v]
                 [_ p]))

             (define (prog/equiv p v)
               ((default-equiv)
                (program-output p)
                v))

             ;;;;
             ;; Task metafunctions

             (define-metafunction Lang
               task:settled? : σ v -> boolean
               [(task:settled? (_ (... ...) (x "done") _ (... ...))
                               (struct _ (... ...) [status (ptr x)] _ (... ...)))
                #true]
               [(task:settled? (_ (... ...) (x "failed") _ (... ...))
                               (struct _ (... ...) [status (ptr x)] _ (... ...)))
                #true]
               [(task:settled? _ _) #false])

             (define-metafunction Lang
               task:allocate : σ label -> (σ v)
               [(task:allocate σ_0 label)
                (σ_1 (struct
                       [parent v_parent]
                       [status (ptr x_status)]
                       [value (ptr x_value)]
                       [awaited (ptr x_awaited)]
                       [cancelled (ptr x_cancelled)]
                       [waiters (ptr x_waiters)]))

                (where/error v_parent ,(if (equal? (term root) (term label))
                                           (term (list))
                                           (term (list (ptr label)))))
                (where/error (x_status x_value x_awaited x_cancelled x_waiters)
                             (gensyms σ_0 (status value awaited cancelled waiters)))
                (where/error σ_1 (ext σ_0
                                      (x_status "running")
                                      (x_value (void))
                                      (x_awaited #false)
                                      (x_cancelled #false)
                                      (x_waiters (list))))])

             (define-metafunction Lang
               task:create-new : label -> e
               [(task:create-new label)
                (struct
                  [parent label]
                  [status (box "running")]
                  [value (box (void))]
                  [awaited (box #false)]
                  [cancelled (box #false)]
                  [waiters (box (list))])])

             (define-metafunction Lang
               task:set-done! : e e -> e
               [(task:set-done! e_s e)
                (let ([s e_s])
                  (begin (set-box! (field value s) e)
                         (set-box! (field status s) "done")))])

             (define-metafunction Lang
               task:set-failed! : e e -> e
               [(task:set-failed! e_s e)
                (let ([s e_s])
                  (begin (set-box! (field value s) e)
                         (set-box! (field status s) "failed")))])

             (define-metafunction Lang
               task:set-cancelled! : e -> e
               [(task:set-cancelled! e)
                (set-box! (field cancelled e) #true)])

             (define-metafunction Lang
               task:is-cancelled? : e -> e
               [(task:is-cancelled? e)
                (unbox (field cancelled e))])

             (define-metafunction Lang
               task:is-completed? : e -> e
               [(task:is-completed? e)
                (let ([x_status_ (unbox (field status e))])
                  (if (equal? x_status_ "done") #true
                      (equal? x_status_ "failed")))])

             (define-metafunction Lang
               task:get-result : v -> e
               [(task:get-result v)
                (if (equal? "done" (unbox (field status v)))
                    (unbox (field value v))
                    (if (equal? "failed" (unbox (field status v)))
                        (throw (unbox (field value v)))
                        (throw "IME: `get-result` called before result was ready")))])

             (define-metafunction Lang
               task:add-waiter! : e (x v) -> e
               [(task:add-waiter! e (x v))
                (let ([s e])
                  (set-box! (field waiters s)
                            (cons (list (ptr x) v) (unbox (field waiters s)))))])

             (define-metafunction Lang
               task:get-waiters : e -> e
               [(task:get-waiters e)
                (unbox (field waiters e))])

             ;;;;
             ;; Queue/Signals metafunctions

             (define-metafunction Lang
               Q:pop : Q -> ((label v) Q) or empty
               [(Q:pop ()) empty]
               [(Q:pop ((label v) (label_s v_s) (... ...)))
                ((label v) ((label_s v_s) (... ...)))])

             (define-metafunction Lang
               Q:push : Q (label v) (... ...) -> Q
               [(Q:push (any_s (... ...)) any_el (... ...))
                (any_s (... ...) any_el (... ...))])

             (define-metafunction Lang
               T:push : T (t label v) (... ...) -> T
               [(T:push  (any_0 (... ...)) any_1 (... ...))
                (any_0 (... ...) any_1 (... ...))])

             (define-metafunction Lang
               T:pop : t T -> ((label v) T) or none
               [(T:pop t_0 ((t_a label_a v_0) (... ...) (t label v) (t_b label_b v_1) (... ...)))
                ((label v) ((t_a label_a v_0) (... ...) (t_b label_b v_1) (... ...)))

                (side-condition (< (term t) (term t_0)))
                (side-condition (andmap (lambda (i) (< (term t) i)) (term (t_a (... ...)))))]
               [(T:pop t T) none]))))]))
