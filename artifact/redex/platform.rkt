#lang racket/base

(require (for-syntax racket/base syntax/parse)
         (only-in racket/list empty? shuffle flatten)
         (only-in racket/function identity)
         (prefix-in lib: (submod "core.rkt" niceties))
         racket/match
         redex/reduction-semantics
         "core.rkt")

(provide (all-defined-out))

(struct nondeterministic exn:fail:user (prog results))

;; Extract the root thread's value from a final program state. Language
;; modules also get a macro-generated copy; this generic one serves
;; clients (e.g. fuzz/main.rkt) that work across languages.
(define (program-output p)
  (match p
    [`(,_t ,_H ,_Q ,_T ((thread (root ,v)) ,_ ...)) v]
    [_ p]))

;; Reduce the `term` using `rule`.
;;
;; If `max-steps` is provided the reduction will be capped at that many times, otherwise, it could loop forever
;; If the reduction is `deterministic?` a form that reduces to multiple results is considered an error; a `nondeterministic` exception is thrown.
;; The function `α-equiv?` is used to filter programs that are alpha equivalent. By default syntactic equivalence `equal?` is used.
(define (reduce rule
                term
                #:interval [interval 500 #;milliseconds]
                #:deterministic? [det? #false]
                #:max-steps [max-steps #false]
                #:α-equiv? [α-equiv? equal?])
  (define iterator
    (if (real? max-steps)
        (in-range max-steps)
        (in-naturals)))
  (for/fold ([term term]
             [iterated? #false]
             #:result (and iterated? term))
            ([_ iterator]
             #:do [(define next-progs (apply-reduction-relation rule term))]
             #:break (empty? next-progs))
    (match next-progs
      [(list reduced) (values reduced #true)]
      [many
       (if det?
           (raise (nondeterministic term many))
           (values (car (shuffle many)) #true))])))

(struct in-set-evaluation exn:fail:user (prog result results))

(define-syntax-rule (with-exn-handler body)
  (with-handlers ([in-set-evaluation?
                   (lambda (e)
                     (eprintf "program reduced outside of its set: ~s~%~%expected: ~s~%got:~s~%"
                              (in-set-evaluation-prog e)
                              (in-set-evaluation-results e)
                              (in-set-evaluation-result e))
                     #false)])
    body
    #true))

;; A testing help that asserts, after each evaluation of `term` using the reduction relation `rule`, the value
;; extracted from the result using `extract` is tested for membership in results using `equiv?`. A maximum of
;; `iterations` iterations are performed.
(define (evaluates-in-set rule
                          term
                          results
                          #:iterations [iters 25]
                          #:extract-result extract
                          #:equiv? [equiv? equal?])
  (for ([_ (in-range iters)])
    (define final (reduce rule term #:deterministic? #false))
    (define result (extract final))
    (unless (and result (member result results equiv?))
      (raise
       (in-set-evaluation "evaluated out of set" (current-continuation-marks) term result results)))))

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
        (~optional (~seq #:def-exn-reduction red/exn/lang:id))
        #:with-base-lang BaseLang:id
        #:with-base-reduction red/base
        (~optional (~and #:single-threaded single-threaded?))
        (~optional (~and #:serial-dispatch serial-dispatch?))
        grammar-rule:expr ...
        (~optional (~seq #:binding-forms bf:expr ...)))
     ;; #:single-threaded -> synchronous code runs unbounded (an infinite loop
     ;;   blocks the runtime). #:serial-dispatch -> the scheduler dispatches like
     ;;   a real event loop (run-to-completion, microtasks before macrotasks),
     ;;   making the runtime deterministic. They are independent: trio is
     ;;   #:single-threaded but NOT #:serial-dispatch, because its structured-
     ;;   concurrency cancellation deadlocks under serial dispatch (a trio-model
     ;;   issue to resolve separately).
     #:with single? (if (attribute single-threaded?) #'#t #'#f)
     #:with serial? (if (attribute serial-dispatch?) #'#t #'#f)
     (with-unhygenic
      #'Lang
      (make-big-step async/main
                     step
                     value?
                     program-output
                     prog/equiv
                     Q:pop Q:push Q:empty
                     T:pop T:push T:empty T:next-signal-at T:pop-cancelled
                     sys/idle?
                     store:find-unawaited-error
                     store:get-pending-tasks
                     store:get-uncancelled-tasks
                     task:settled?
                     task:cancelled?
                     task:uncancel
                     task:allocate
                     task:allocate-as
                     task:allocate-dependency
                     task:is-task?
                     task:get-dependents
                     task:set-done!
                     task:set-failed!
                     task:set-cancelled!
                     task:set-awaited!
                     task:is-cancelled?
                     task:is-completed?
                     task:continue-with
                     task:get-result
                     task:add-self-as-dependent!
                     task:cancel-dependencies
                     task:wait-on-dependencies
                     task:await-dependencies
                     )
      #'
      (begin
        ;; The systems language `SysLang` is the base lambda calculus, either LC or LC+Exn,
        ;; extended with a multithreaded platform. There are also the OmniScient hooks:
        ;; `os/block`, `os/time`, `os/io`, and `os/start-later`.
        (define-extended-language
         SysLang
         BaseLang
         (e ::= ....
                (os/block e) ;; block the current thread until the async work is done
                (os/time) ;; get the current time step
                (os/io e_delay e) ;; perform an IO operation that takes (at least) `e_delay` time steps and returns `e`
                (os/start-soon e) ;; schedule the evaluation of `e` with the frame label `e_label`
                (os/start-later e_time label e)) ;; schedule the signal of operation `e` at (at least) timestep `e_time` with the frame label `e_label`
         (E ::= ....
                (os/block E)
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

        (define-extended-language Lang SysLang grammar-rule ... (~? (~@ #:binding-forms bf ...)))

        ;; Given a reduction relation `red` and a `term`, evalaute the term many times
        ;; using the provided relation. If the term is `det?`, reducing to multiple
        ;; forms is considered an error, if not, a random reduction is chosen and continued with.
        ;;
        ;; We want to use non-deterministic reductions with the threaded model. The goal is *not*
        ;; to model fine-grained memory access, so we take larger steps as a regular system would.
        ;; Decisions are then made when as async/lambda or await form is reached in one of the threads.
        ;;
        ;; The step cap must be > 1: synchronous code (and the system's scheduling
        ;; chunk) runs atomically up to the next async decision point. A cap of 1
        ;; interleaves at every micro-step, which splits `await`'s
        ;; check-then-register across steps and loses wakeups (a completed task
        ;; can fire its waiters between the `task:is-completed?` read and the
        ;; `task:add-self-as-dependent!` registration). 50 is a coarse bound that
        ;; lets a thread reach its next async point in one step for the programs
        ;; we generate.
        (define big-step-max-steps 50)
        (define (big-step red term #:deterministic? [det? #true] #:allow-infinity? [inf? #f])
          (with-handlers ([nondeterministic? (lambda (e) 'stuck)])
            (let* ([α-equiv? (lambda (a b) (alpha-equivalent? Lang a b))]
                   [reduced
                    (reduce red term
                            #:deterministic? det?
                            #:max-steps (if inf? #false big-step-max-steps)
                            #:α-equiv? α-equiv?)])
              (when (α-equiv? term reduced)
                (raise 'big-step "form reduced to itself"))
              reduced)))

        (define -->sys/sync
          (extend-reduction-relation (extend-reduction-relation red/base SysLang) Lang))

        (define red/lang
          (reduction-relation
           Lang
           #:domain (t σ Q T P)

           [-->
            (t_0 σ_0 Q T (FS_0 (... ...) (thread (label e_0) F (... ...)) FS_1 (... ...)))
            (t_1 σ_1 Q T (FS_0 (... ...) (thread (label e_1) F (... ...)) FS_1 (... ...)))
            (side-condition (not (value? (term e_0))))
            (where (σ_1 e_1) ,(big-step -->sys/sync (term (σ_0 e_0)) #:allow-infinity? single?))
            (where/error t_1 t_0)
            "base-lang/reduce"]

           [-->
            (t_0 σ
                 Q
                 T
                 (FS_0 (... ...) (thread (label (in-hole E (os/time))) F (... ...)) FS_1 (... ...)))
            (t_1 σ Q T (FS_0 (... ...) (thread (label (in-hole E t_0)) F (... ...)) FS_1 (... ...)))
            (where/error t_1 t_0)
            "os/time"]

           [-->
            (t_0 σ_0
                 Q
                 T
                 (FS_0 (... ...) (thread (label (in-hole E (os/io t v))) F (... ...)) FS_1 (... ...)))
            (t_1 σ_2
                 Q
                 T
                 (FS_0 (... ...)
                       (thread (x_io (os/start-later (+ (os/time) t)
                                                     x_io
                                                     (lambda (none)
                                                       (begin
                                                         none
                                                         (task:set-done! x_io v)
                                                         (os/start-soon (task:get-dependents x_io))))))
                               (label (in-hole E x_io))
                               F
                               (... ...))
                       FS_1
                       (... ...)))
            (where/error (σ_1 x_io v_task) (task:allocate σ_0))
            (where/error σ_2 (ext1 σ_1 (x_io v_task)))
            (where/error t_1 t_0)
            "os/io"]

          [-->
            (t_0 σ
                 Q_0
                 T
                 (FS_0 (... ...)
                       (thread (label (in-hole E (os/start-soon (list (list (ptr label_waiting) v) (... ...)))))
                               F (... ...))
                       FS_1 (... ...)))
            (t_1 σ
                 Q_1
                 T
                 (FS_0 (... ...) (thread (label (in-hole E (void))) F (... ...)) FS_1 (... ...)))

            (where/error Q_1 (Q:push Q_0 (label_waiting v) (... ...)))
            (where/error t_1 t_0)
            "os/start-soon"]

           [-->
            (t_0 σ
                 Q
                 T_0
                 (FS_0 (... ...)
                       (thread (label (in-hole E (os/start-later t x v))) F (... ...))
                       FS_1
                       (... ...)))
            (t_1 σ
                 Q
                 T_1
                 (FS_0 (... ...) (thread (label (in-hole E (void))) F (... ...)) FS_1 (... ...)))
            (where/error T_1 (T:push T_0 (t x v)))
            (where/error t_1 t_0)
            "os/start-later"]

           [--> ;; NOTE: the default for exiting the runtime is to wait for all tasks to be completed.
            (t_0 σ () () ((thread (root (in-hole E (os/block v_awaitable)))) (thread) ..._1))
            (t_1 σ () () ((thread (root (in-hole E (task:get-result v_awaitable)))) (thread) ..._1))
            (where #true (task:is-task? v_awaitable))
            (where #true (task:settled? σ v_awaitable))
            (where/error t_1 t_0)
            "os/block-done"]

           [-->
            (t_0 σ ()
                 ((t_a label_a v_a) (... ...) (t_x label_x v_x) (t_b label_b v_b) (... ...))
                 ((thread (root (in-hole E (os/block v_awaitable)))) (thread) ..._1))
            (t_1 σ ()
                 ((t_a label_a v_a) (... ...) (t_x label_x v_x) (t_b label_b v_b) (... ...))
                 ((thread (root (in-hole E (os/block v_awaitable)))) (thread) ..._1))
            (where #true (task:is-task? v_awaitable))
            (where #false (task:settled? σ v_awaitable))
            (side-condition (< (term t_0) (term t_x)))
            ;; LOGICAL TIME: jump the clock to ANY pending deadline rather than
            ;; crawling +1. `os/io n` means the timer fires after AT LEAST n
            ;; steps, so the clock may pass a due-but-undelivered timer -- that
            ;; is what lets a 3-step timer fire after a 4-step one (deadline
            ;; inversion, observed in real runtimes under scheduler jitter).
            ;; This is the ONLY rule that advances time; every other rule is
            ;; instantaneous in logical time (t_1 = t_0), so deadlines reflect
            ;; wait time, not how much computation happened in between.
            (where/error t_1 t_x)
            "os/block-wait"]

           [-->
            (t_0 (any_before (... ...) (x v) any_after (... ...)) Q T PS)
            (t_1 (any_before (... ...) any_after (... ...)) Q T PS)
            (side-condition
              (let ([remaining-state (term (Q T PS any_before (... ...) any_after (... ...)))])
                (not (memq (term x) (flatten remaining-state)))))
            (where/error t_1 t_0)
            "sys/gc"]

           [-->
            (t_0 σ Q_0 T ((thread F F_rs (... ...)) (... ...) (thread) FS_1 (... ...)))
            (t_1 σ
                 Q_1
                 T
                 ((thread F F_rs (... ...)) (... ...)
                                            (thread (label_waiting (v_thunk (void))))
                                            FS_1
                                            (... ...)))
            (where ((label_waiting v_thunk) Q_1) (Q:pop Q_0))
            (where #false (task:cancelled? σ label_waiting))
            ;; SINGLE-THREADED: a real event loop never starts a microtask while
            ;; another job is still running -- dispatch only when all threads idle.
            (side-condition
             (or (not serial?)
                 (term (sys/idle? ((thread F F_rs (... ...)) (... ...) (thread) FS_1 (... ...))))))
            (where/error t_1 t_0)
            "sys/schedule"]

          [-->
            (t_0 σ Q_0 T ((thread F F_rs (... ...)) (... ...) (thread) FS_1 (... ...)))
            (t_1 σ Q_1 T ((thread F F_rs (... ...)) (... ...) (thread) FS_1 (... ...)))
            (where ((label_waiting v_thunk) Q_1) (Q:pop Q_0))
            (where #true (task:cancelled? σ label_waiting))
            ;; SINGLE-THREADED: same idle gate as sys/schedule (cancelled microtask).
            (side-condition
             (or (not serial?)
                 (term (sys/idle? ((thread F F_rs (... ...)) (... ...) (thread) FS_1 (... ...))))))
            (where/error t_1 t_0)
            "sys/schedule-cancelled"]

           [-->
            (t σ Q T (FS_0 (... ...) (thread (label (void)) F_rs (... ...)) FS_1 (... ...)))
            (t σ Q T (FS_0 (... ...) (thread F_rs (... ...)) FS_1 (... ...)))

            (side-condition (not (eq? 'root (term label))))
            "sys/thread-pop-frame"]

           ;; ANY due timer may fire (deadline <= now), not just the earliest:
           ;; `os/io n` promises AT LEAST n steps, so among simultaneously-due
           ;; timers the delivery order is unconstrained. Direct ellipsis match
           ;; -- a rule may be nondeterministic where a metafunction (the old
           ;; T:pop) must not be.
           [-->
            (t_0 σ Q_0 ((t_a label_a v_a) (... ...) (t_d label v) (t_b label_b v_b) (... ...)) P)
            (t_1 σ Q_1 ((t_a label_a v_a) (... ...) (t_b label_b v_b) (... ...)) P)
            (side-condition (<= (term t_d) (term t_0)))
            (where #false (task:cancelled? σ label))
            ;; SINGLE-THREADED: timers (macrotasks) wait until the call stack is
            ;; empty AND every microtask is drained (micro-before-macro + RTC).
            (side-condition
             (or (not serial?)
                 (and (term (Q:empty Q_0)) (term (sys/idle? P)))))
            (where/error Q_1 (Q:push Q_0 (label v)))
            (where/error t_1 t_0)
            "sys/signal"]))

        (~? (~@ (define red/exn/lang
                  (extend-reduction-relation
                    red/lang
                    Lang

                    [-->
                      (t_0 σ_0 Q T (FS_0 (... ...) (thread (label (in-hole E (os/io t v))) F (... ...)) FS_1 (... ...)))
                      (t_1 σ_2 Q T (FS_0 (... ...) (thread
                                                    (x_io (os/start-later (+ (os/time) t)
                                                                          x_io
                                                                          (lambda (none)
                                                                            (begin (catch (lambda (e) (task:set-failed! x_io e))
                                                                                     (begin none
                                                                                            (task:set-done! x_io v)))
                                                                                   (os/start-soon (task:get-dependents x_io))))))
                                                    (label (in-hole E x_io)) F (... ...))
                                        FS_1 (... ...)))

                      (where/error (σ_1 x_io v_task) (task:allocate σ_0))
                      (where/error σ_2 (ext1 σ_1 (x_io v_task)))
                      (where/error t_1 t_0)
                      "os/io"]

                    [-->
                      (t_0 σ Q_0 T ((thread F F_rs (... ...)) (... ...) (thread) FS_1 (... ...)))
                      (t_1 σ Q_1 T ((thread F F_rs (... ...)) (... ...)
                                            (thread (label_waiting (throw-in v_thunk "cancelled"))) FS_1 (... ...)))
                      (where ((label_waiting v_thunk) Q_1) (Q:pop Q_0))
                      (where #true (task:cancelled? σ label_waiting))
                      ;; SINGLE-THREADED: idle gate, as on the base sys/schedule.
                      (side-condition
                       (or (not serial?)
                           (term (sys/idle? ((thread F F_rs (... ...)) (... ...) (thread) FS_1 (... ...))))))
                      (where/error t_1 t_0)
                      "sys/schedule-cancelled"]

                    ;; ANY cancelled timer may drain (direct ellipsis match on T:
                    ;; a rule may be nondeterministic; the old T:pop-cancelled
                    ;; METAFUNCTION faulted -- "matched 3 different ways, 2
                    ;; different results" -- whenever two cancelled timers were
                    ;; pending, since metafunctions must be functions).
                    [-->
                      (t_0 σ Q_0 (any_th (... ...) (t_c label v) any_tt (... ...)) P)
                      (t_1 σ Q_1 (any_th (... ...) any_tt (... ...)) P)
                      (where #true (task:cancelled? σ label))
                      ;; SINGLE-THREADED: macrotask gate, as on the base sys/signal.
                      (side-condition
                       (or (not serial?)
                           (and (term (Q:empty Q_0)) (term (sys/idle? P)))))
                      (where/error Q_1 (Q:push Q_0 (label v)))
                      (where/error t_1 t_0)
                      "sys/signal-cancel"]

                    [-->
                      (t_0 σ Q T (_ ..._1 (thread (throw v)) _ ..._2))
                      (t_1 σ Q T ((thread (throw v)) (thread) ..._1 (thread) ..._2))
                      (where/error t_1 t_0)
                      "sys/halt"]))))


        ;;;;
        ;; Std Implementations

        ;; Provided a base program as `stx`, wrap that program in an evaluation context `P` using `thrds` threads.
        (define-syntax (async/main stx)
          (syntax-parse stx
            [(_ (~optional (~seq #:threads thrds:integer)) e)
             (define workers
               (for/list ([i (in-range 1 (syntax-e #'(~? thrds 1)))])
                 '(thread)))
             #`(term-let ([(thrd (... (... ...))) '#,workers])
                         (term #;t
                               #;σ
                               (0 () #;Q () #;T () #;PS ((thread (root e)) thrd (... (... ...))))
                               #:lang Lang))]))

        ;; Provided a small-step rule define on `Lang`, create a big step version defined for same language.
        (define (make-big-step red)
          (reduction-relation
           Lang
           #:domain (t σ Q T P)
           [-->
            (t_0 σ_0 Q_0 T_0 P_0)
            (t_1 σ_1 Q_1 T_1 P_1)
            (where (t_1 σ_1 Q_1 T_1 P_1)
                   ,(big-step red (term (t_0 σ_0 Q_0 T_0 P_0)) #:deterministic? #false))
            "sys-lang/reduce"]))

        (define (value? t)
          (redex-match? Lang v t))

        (define (program-output p)
          (match p
            [`(,_t ,_H ,_Q ,_T ((thread (root ,v)) ,_ (... ...))) v]
            [_ p]))

        (define (prog/equiv p v)
          ((default-equiv) (program-output p) v))

        ;;;;
        ;; Store metafunctions

        (define-metafunction
         Lang
         store:find-unawaited-error : σ -> (some v) or none
         [(store:find-unawaited-error (_ (... ...) ;; some things
                                         (_ (struct _ (... ...)
                                              [status (ptr x_status)]
                                              [value (ptr x_error)]
                                              [awaited (ptr x_awaited)]
                                              _ (... ...))) ;; a bound task value T
                                         _ (... ...)
                                         (x_status "failed") ;; failed status for task T
                                         _ (... ...)
                                         (x_error v_error) ;; the error value for task T
                                         _ (... ...)
                                         (x_awaited #false) ;; task T has not been awaited
                                         _ (... ...)))
          (some v_error)]
         [(store:find-unawaited-error _) none])

        (define-metafunction Lang
          store:get-pending-tasks : σ -> (v (... ...))
          [(store:get-pending-tasks ()) ()]
          [(store:get-pending-tasks (name σ ((_ v_task) any_rest (... ...))))
           (v_task any_oths (... ...))
           (where (struct _ (... ...) [status (ptr x_status)] _ (... ...)) v_task)
           (where "running" (lookup σ x_status))
           (where/error (any_oths (... ...)) (store:get-pending-tasks (any_rest (... ...))))]
          [(store:get-pending-tasks (_ any_rest (... ...)))
           (store:get-pending-tasks (any_rest (... ...)))])

        (define-metafunction Lang
          store:get-uncancelled-tasks : σ -> (v (... ...))
          [(store:get-uncancelled-tasks ()) ()]
          [(store:get-uncancelled-tasks (name σ ((_ v_task) any_rest (... ...))))
           (v_task any_oths (... ...))
           (where (struct _ (... ...) [cancelled (ptr x_cancelled)] _ (... ...)) v_task)
           (where #false (lookup σ x_cancelled))
           (where/error (any_oths (... ...))
                        (store:get-uncancelled-tasks (any_rest (... ...))))]
          [(store:get-uncancelled-tasks (_ any_rest (... ...)))
           (store:get-uncancelled-tasks (any_rest (... ...)))])

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
          task:cancelled? : σ label -> boolean
          [(task:cancelled? σ x)
            ,(ormap identity (term (boolean (task:cancelled? σ x_parent) (... ...))))
            (where/error v (lookup σ x))
            (where/error #true (task:is-task? v))
            (where/error (struct _ (... ...)
                                 [parents (ptr x_parents)]
                                 _ (... ...)
                                 [cancelled (ptr x_cancelled)]
                                 _ (... ...)) v)
            (where/error boolean (lookup σ x_cancelled))
            (where/error (list (ptr x_parent) (... ...)) (lookup σ x_parents))]
          [(task:cancelled? σ x)
            boolean
            (where/error v (lookup σ x))
            (where/error #true (task:is-task? v))
            (where/error (struct _ (... ...)
                           [parents (ptr x_parent)]
                           _ (... ...)
                           [cancelled (ptr x_cancelled)]
                           _ (... ...)) v)
            (where/error boolean (lookup σ x_cancelled))
            (where (list) (lookup σ x_parent))])

        ;; Reset a task's own cancelled flag, e.g. after the cancellation has
        ;; been delivered to the task as an exception.
        (define-metafunction Lang
          task:uncancel : σ label -> σ
          [(task:uncancel σ x)
            (ext1 σ (x_cancelled #false))
            (where/error v (lookup σ x))
            (where/error #true (task:is-task? v))
            (where/error (struct _ (... ...)
                           [cancelled (ptr x_cancelled)]
                           _ (... ...)) v)])

        (define-metafunction Lang
         task:allocate-as : σ x -> (σ x v)
         [(task:allocate-as σ_0 x_me)
          (σ_1 x_me
               (struct
                 [self (ptr x_me)]
                 [parents (ptr x_parent)]
                 [children (ptr x_child)]
                 [status (ptr x_status)]
                 [value (ptr x_value)]
                 [awaited (ptr x_awaited)]
                 [cancelled (ptr x_cancelled)]
                 [waiters (ptr x_waiters)]))
          (where/error (x_parent x_child x_status x_value x_awaited x_cancelled x_waiters)
                       (gensyms σ_0 (parents children status value awaited cancelled waiters)))
          (where/error σ_1
                       (ext σ_0
                            (x_parent (list))
                            (x_child (list))
                            (x_status "running")
                            (x_value (void))
                            (x_awaited #false)
                            (x_cancelled #false)
                            (x_waiters (list))))])

        (define-metafunction Lang
         task:allocate : σ -> (σ x v)
         [(task:allocate σ)
          (task:allocate-as σ x)
          (where/error (x) (gensyms σ (task)))])

      (define-metafunction Lang
        task:add-dependency : σ label label -> σ
        [(task:add-dependency σ label _)
         σ
         (side-condition (eq? (term label) 'root))]
        [(task:add-dependency σ x_parent x_child)
         (any_0 (... ...)
          (x_parent_children (list (ptr x_child) v_parents_children (... ...)))
          any_1 (... ...))

         (where/error (struct _ (... ...) [children (ptr x_parent_children)] _ (... ...))
                      (lookup σ x_parent))
         (where/error (any_0 (... ...)
                       (x_parent_children (list v_parents_children (... ...)))
                       any_1 (... ...)) σ)])

      (define-metafunction Lang
       task:allocate-dependency : σ label -> (σ x v)
       [(task:allocate-dependency σ label)
        (task:allocate σ)
        (side-condition (eq? (term label) 'root))]
       [(task:allocate-dependency σ x)
        (task:allocate-as σ_0 x_me)
        (where/error (x_me) (gensyms σ (task)))
        (where/error σ_0 (task:add-dependency σ x x_me))])

      ;;;;
      ;; User space constructs

        (define-metafunction Lang
          task:is-task? : v -> boolean
          [(task:is-task? (struct [self (ptr x_me)] 
                                  [parents (ptr x_parent)]
                                  [children (ptr x_child)]
                                  [status (ptr x_status)]
                                  [value (ptr x_value)]
                                  [awaited (ptr x_awaited)]
                                  [cancelled (ptr x_cancelled)]
                                  [waiters (ptr x_waiters)]))
          #true]
          [(task:is-task? _) #false])

        (define-metafunction Lang
          task:set-done! : x e -> e
          [(task:set-done! x e)
           (begin
             (set-box! (field value x) e)
             (set-box! (field status x) "done"))])

        (define-metafunction Lang
          task:set-failed! : x e -> e
          [(task:set-failed! x e)
           (begin
             (set-box! (field value x) e)
             (set-box! (field status x) "failed"))])

        (define-metafunction Lang
          task:set-cancelled! : e -> e
          [(task:set-cancelled! e)
          (set-box! (field cancelled e) #true)])

        (define-metafunction Lang
          task:set-awaited! : e -> e
          [(task:set-awaited! e)
          (set-box! (field awaited e) #true)])

        (define-metafunction Lang
          task:is-completed? : e -> e
          [(task:is-completed? e)
          (let ([status (unbox (field status e))])
            (if (equal? status "done")
                #true
                (equal? status "failed")))])

        (define-metafunction Lang
          task:continue-with : v x -> e
          [(task:continue-with v x)
           (lambda (none)
             (catch (lambda (e) (throw-in x e))
                    (begin none
                           (let ([status (unbox (field status v))]
                                 [val (unbox (field value v))])
                             (if (equal? status "done")
                                 (x val)
                                 (if (equal? status "failed")
                                     (throw-in x val)
                                     (throw "IME: `continue-with` invoked incorrectly")))))))])

        (define-metafunction Lang
          task:is-cancelled? : e -> e
          [(task:is-cancelled? e)
            (unbox (field cancelled e))])

        (define-metafunction Lang
          task:get-result : e -> e
          [(task:get-result e)
           (let ([v e])
             (if (equal? "done" (unbox (field status v)))
                 (unbox (field value v))
                 (if (equal? "failed" (unbox (field status v)))
                     (throw (unbox (field value v)))
                     (throw "IME: `get-result` called before result was ready"))))])

        (define-metafunction Lang
          task:add-self-as-dependent! : e (x e) -> e
          [(task:add-self-as-dependent! e (x e_v))
          (let ([child e] [parent x])
            (begin
              (set-box! (field parents child)
                        (cons (ptr x)
                              (unbox (field parents child))))
              (set-box! (field children parent)
                        (cons (field self child)
                              (unbox (field children parent))))
              (set-box! (field waiters child)
                        (cons (list (ptr x) e_v)
                              (unbox (field waiters child))))))])

        (define-metafunction Lang
          task:get-dependents : e -> e
          [(task:get-dependents e)
                (unbox (field waiters e))])


        (define-metafunction Lang
          task:cancel-dependencies : x -> e
          [(task:cancel-dependencies x)
           (cancel x)
           #;(lib:for-each (lambda (t) (cancel (unbox t)))
             (unbox (field children x)))])

        (define-metafunction Lang
          task:wait-on-dependencies : x -> e
          [(task:wait-on-dependencies x)
           (lib:for-each (lambda (p)
                          (let ([t (unbox p)])
                            (if (task:is-completed? t)
                                (void)
                                (shift k (task:add-self-as-dependent! t (x k))))))
             (unbox (field children x)))])

        (define-metafunction Lang
          task:await-dependencies : x -> e
          [(task:await-dependencies x)
           (lib:for-each (lambda (p)
                          (let ([t (unbox p)])
                            (if (task:is-completed? t)
                                (void)
                                (begin
                                  (shift k (task:add-self-as-dependent! t (x k)))
                                  (task:get-result t)))))
             (unbox (field children x)))])

        ;;;;
        ;; Queue/Signals metafunctions

        ;; #true iff no thread is runnable: each thread is either an empty worker
        ;; slot or the root parked on an (os/block <task>) it is still waiting
        ;; for. Gates the scheduler in single-threaded runtimes so dispatch
        ;; matches a real event loop (run-to-completion + microtasks before
        ;; macrotasks). A worker mid-job has a reducible top frame, so it falls
        ;; through to #false and the scheduler waits.
        (define-metafunction Lang
          sys/idle? : (FS (... ...)) -> boolean
          [(sys/idle? ()) #true]
          [(sys/idle? ((thread) FS (... ...))) (sys/idle? (FS (... ...)))]
          [(sys/idle? ((thread (root (in-hole E (os/block v_task)))) FS (... ...)))
           (sys/idle? (FS (... ...)))
           (where #true (task:is-task? v_task))]
          [(sys/idle? _) #false])

        (define-metafunction Lang
          Q:pop : Q -> ((label v) Q) or empty
          [(Q:pop ()) empty]
          [(Q:pop ((label v) (label_s v_s) (... ...)))
          ((label v) ((label_s v_s) (... ...)))])

        (define-metafunction Lang
          Q:push : Q (label v) (... ...) -> Q
          [(Q:push (any_s (... ...)) any_el (... ...))
          (any_s (... ...) any_el (... ...))])

        (define-metafunction Lang Q:empty : Q -> boolean
          [(Q:empty ()) #true] 
          [(Q:empty _) #false])

        (define-metafunction Lang
          T:push : T (t label v) (... ...) -> T
          [(T:push (any_0 (... ...)) any_1 (... ...))
          (any_0 (... ...) any_1 (... ...))])

        (define-metafunction
         Lang T:pop : t T -> ((label v) T) or none
         [(T:pop t_0 ((t_a label_a v_0) (... ...) (t label v) (t_b label_b v_1) (... ...)))
          ((label v) ((t_a label_a v_0) (... ...) (t_b label_b v_1) (... ...)))
          (side-condition (<= (term t) (term t_0)))
          (side-condition (andmap (lambda (i) (< (term t) i)) (term (t_a (... ...)))))]
         [(T:pop t T) none])

        (define-metafunction Lang T:empty : T -> boolean
          [(T:empty ()) #true]
          [(T:empty _) #false])

        (define-metafunction Lang
          T:next-signal-at : T -> (some t) or none
          [(T:next-signal-at ()) none]
          [(T:next-signal-at ((t_0 _ _) (t_s _ _) (... ...)))
          (some ,(apply min (term (t_0 t_s (... ...)))))])

        (define-metafunction Lang
          T:pop-cancelled : σ T -> (some (label v T)) or none
          [(T:pop-cancelled σ (any_head (... ...) (_ label v) any_tail (... ...)))
          (some (label v (any_head (... ...) any_tail (... ...))))
          (where #true (task:cancelled? σ label))]
          [(T:pop-cancelled _ _) none])))]))

