#lang racket

(require racket/generic
         racket/stxparam
         racket/control
         racket/async-channel
         (for-syntax syntax/parse))

(provide define/async
         lambda/async
         await
         is-cancelled?
         spawn
         cancel
         block
         io/delay
         exn:cancelled?

         *pool-size*
         *eagerness*
         *suspension*
         *extent*
         *ref-strength*
         *destruction*
         *propagation*
         *awareness*
         *direction*
         *persistence*)

;; =========
;; ECOSYSTEM
;; =========

(define-syntax-rule (ice e ...)
  (raise e ...))

(define-generics awaitable
  (get-awaiter awaitable))


(define-generics awaiter
  (is-completed? awaiter)
  (on-completed! awaiter k)
  (get-result awaiter))


(struct exn:userland exn:fail () #:transparent)

(struct exn:cancelled exn:userland () #:transparent)

(struct suspended (awaiter coro) #:transparent)

(define (assert-resume! v)
  (cond
    [(exn:cancelled? v)
     (raise exn:cancel)]
    [(null? v)]
    [else (ice "unexpected resumption value" v)]))


(define exn:cancel
  (exn:cancelled "cancelled" (current-continuation-marks)))


(define (cancelled?)
  (define t (*current-task*))
  (and t (task-cancelled? t) #t))


(define-syntax-parameter is-cancelled?
  (lambda (stx)
    (raise-syntax-error
     'is-cancelled? "is-cancelled? available inside a Swift async function" stx)))


;; Requires: awareness != #f, direction = simultaneous.
;; Polling for cancellation is only meaningful when the task can observe it (aware)
;; and all tasks in the subtree are marked simultaneously (simultaneous direction).
(define (is-cancelled?-impl)
  (when (and (eq? (*direction*) 'simultaneous)
             (not (eq? (*eagerness*) 'lazy)))
    (raise-syntax-error "`is-cancelled?` only available for simultaneous awareness"))
  (cancelled?))


(define-syntax-parameter cancel
  (lambda (stx)
    (raise-syntax-error
     'cancel "cancel only available inside an async function" stx)))


(define (cancel-impl t)
  (unless (*awareness*)
    (raise-syntax-error 'cancel "cancel not available in this language"))
  (unless (task? t)
    (raise-argument-error 'cancel "task?" t))
  (cancel! t))


(define (hold-task t)
  (if (eq? (*ref-strength*) 'weak) (make-weak-box t) t))

(define (deref-task ref)
  (if (weak-box? ref) (weak-box-value ref) ref))

;; A coroutine is an inert async computation. Calling an async function
;; in lazy mode returns one of these — no task exists yet, nothing is
;; registered with the runtime. It becomes a task only when spawned or awaited.
;;
;; Uniform resume protocol:
;;   (activate '())          → normal start/continue, returns body thunk
;;   (activate exn:cancelled) → raises via assert-resume!
(struct coroutine (activate))

(struct task (state value callbacks parent children cancelled? cancel-callbacks
                    errors thunk mutex body-done?)
  #:mutable

  #:methods gen:awaitable
  [ (define (get-awaiter t) t) ]

  #:methods gen:awaiter
  [ (define (is-completed? t)
      (settled? t))

    (define (on-completed! t k)
      (task-on-complete! t k))

    (define (get-result t)
      (cond
        [(pending? t) (ice "task is still running")]
        [(failed? t) (raise (task-value t))]
        [(completed? t) (task-value t)])) ])


(define *current-task* (make-parameter #f))


;; NOTE: awaited + weak is semantically problematic. Weak refs allow the
;; runtime to lose track of a task (e.g., timer-reg weak-box emptied),
;; but awaited demands run-to-completion. Re-registration keeps the task
;; alive but cannot restore lost scheduling state. No current language uses
;; this combination.
(define (task-destructor t)
  (unless (task? t)
    (ice "not a task?" t))
  (when (pending? t)
    (case (*destruction*)
      [(terminated) (terminate! t)]
      [(cancelled)  (cancel! t)]
      [(awaited)
       (define rt (assert-runtime))
       (will-register (runtime-will-executor rt) t task-destructor)])))


(define (inc-pending!)
  (define rt (assert-runtime))
  (call-with-semaphore (runtime-pending-lock rt)
    (lambda ()
      (set-box! (runtime-pending-count rt)
                (add1 (unbox (runtime-pending-count rt)))))))

(define (dec-pending!)
  (define rt (unbox *runtime*))
  (when rt
    (call-with-semaphore (runtime-pending-lock rt)
      (lambda ()
        (define n (sub1 (unbox (runtime-pending-count rt))))
        (set-box! (runtime-pending-count rt) n)
        (when (zero? n)
          (semaphore-post (runtime-all-settled rt)))))))

(define (make-pending-task [parent #f])
  (define t (task 'pending #f '() parent '() #f '() '() #f (make-semaphore 1) #f))
  (when (and parent (eq? (*extent*) 'dynamic))
    (with-task-lock parent
      (set-task-children! parent (cons t (task-children parent)))))
  (define rt (assert-runtime))
  (will-register (runtime-will-executor rt) t task-destructor)
  (inc-pending!)
  t)

(define (pending? t) (eq? (task-state t) 'pending))
(define (completed? t) (eq? (task-state t) 'completed))
(define (failed? t) (eq? (task-state t) 'failed))
(define (settled? t) (not (pending? t)))

(define-syntax-rule (with-task-lock t body ...)
  (call-with-semaphore (task-mutex t) (lambda () body ...)))


;; Two-phase task settlement:
;; Phase 1: handle children according to extent/destruction
;; Phase 2: finalize (set state, fire callbacks)
(define (task-settled! t v #:failed? [is-failed #false])
  (unless (pending? t)
    (ice "task already settled" t))

  (set-task-body-done?! t #t)
  (define pending-children
    (filter (lambda (c) (not (settled? c))) (task-children t)))

  (cond
    [(or (null? pending-children) (eq? (*extent*) 'indefinite))
     (finalize-task! t v is-failed)]

    [else
     (when (eq? (*destruction*) 'cancelled)
       (for ([child pending-children])
         (cancel! child)))
     (wait-for-children-then-settle! t v is-failed pending-children)]))


(define (finalize-task! t v is-failed)
  (with-task-lock t
    (when (pending? t)
      (define status (if is-failed 'failed 'completed))
      (set-task-state! t status)
      (set-task-value! t v)

      ;; Propagation: collect child errors and re-raise
      (when (and (eq? (*propagation*) 'destruction) (not is-failed))
        (define child-errors (task-errors t))
        (unless (null? child-errors)
          (set-task-state! t 'failed)
          (set-task-value! t (car child-errors))))

      (set-task-children! t '())
      (for ([callback (reverse (task-callbacks t))])
        (callback t))
      (set-task-callbacks! t '())
      (dec-pending!))))


(define (wait-for-children-then-settle! t v is-failed children)
  (define remaining (box (length children)))
  (for ([child children])
    (task-on-complete! child
                       (lambda (_)
                         (when (and (failed? child) (eq? (*propagation*) 'destruction))
                           (with-task-lock t
                             (set-task-errors! t (cons (task-value child) (task-errors t)))))
                         (define n (with-task-lock t
                                     (define n (sub1 (unbox remaining)))
                                     (set-box! remaining n)
                                     n))
                         (when (zero? n)
                           (finalize-task! t v is-failed))))))


(define (force-terminate-one! t)
  (with-task-lock t
    (unless (settled? t)
      (set-task-state! t 'failed)
      (set-task-value! t exn:cancel)
      (set-task-children! t '())
      (for ([callback (reverse (task-callbacks t))])
        (callback t))
      (set-task-callbacks! t '())
      (dec-pending!))))

(define (terminate! t)
  (for ([child (filter (lambda (c) (not (settled? c))) (task-children t))])
    (terminate! child))
  (force-terminate-one! t))


(define (task-on-complete! t callback)
  (with-task-lock t
    (cond
      [(settled? t) (callback t)]
      [(pending? t)
       (set-task-callbacks! t (cons callback (task-callbacks t)))])))


;; =======
;; RUNTIME
;; =======


(define *runtime* (box #f))

(struct work-item (task-ref coro))

(struct runtime (main thread-pool work-queue threads reactor timer-channel
                      will-executor will-thread
                      pending-count pending-lock all-settled))


(define (assert-runtime)
  (define rt (unbox *runtime*))
  (unless (runtime? rt)
    (raise "No async runtime in current context"))
  rt)


(define (wait-for-thread!)
  (async-channel-get (runtime-thread-pool (assert-runtime))))

(define (release-thread! thd)
  (async-channel-put (runtime-thread-pool (assert-runtime))
                     thd))

(define (schedule-resume! task coro)
  (async-channel-put (runtime-work-queue (assert-runtime))
                     (work-item (hold-task task) coro)))

;; Requires: awareness != #f, persistence != #f (when awareness = aware).
;; Persistence governs whether the cancelled flag is cleared after delivery;
;; this is only meaningful when the task can observe cancellation (aware).
(define (dispatch-work-item! item)
  (define task (deref-task (work-item-task-ref item)))
  (define coro (work-item-coro item))
  (when (and task (pending? task))
    (cond
      [(not (task-cancelled? task))
       (resume! task coro '())]
      [(eq? (*awareness*) 'aware)
       (when (eq? (*persistence*) 'transient)
         (set-task-cancelled?! task #f))
       (resume! task coro exn:cancel)]
      [else
       (force-terminate-one! task)])))

(define (runtime-loop)
  (thread
   (lambda ()
     (let loop ([item (async-channel-get (runtime-work-queue (assert-runtime)))]
                [thd (wait-for-thread!)])
       (thread-send thd
                    (lambda ()
                      (dispatch-work-item! item)
                      (release-thread! thd)))
       (loop (async-channel-get (runtime-work-queue (assert-runtime)))
             (wait-for-thread!))))))



(define (make-worker-thread)
  (thread
   (lambda ()
     (let loop ([thunk (thread-receive)])
       (with-handlers ([exn:userland? void])
         (thunk))
       (loop (thread-receive))))))


;; ==============
;; CONFIGURATION
;; ==============


(define *pool-size* (make-parameter 8))
(define *eagerness* (make-parameter 'eager))
(define *suspension* (make-parameter 'dynamic))
(define *extent* (make-parameter 'indefinite))
(define *ref-strength* (make-parameter 'strong))
(define *destruction* (make-parameter 'terminated))
(define *propagation* (make-parameter 'never))
(define *awareness* (make-parameter #f))
(define *direction* (make-parameter #f))
(define *persistence* (make-parameter #f))


(define (make-runtime)
  (define n-threads (*pool-size*))
  (define work-queue (make-async-channel))
  (define thread-pool (make-async-channel n-threads))
  (define threads
    (for/list ([_ (in-range n-threads)])
      (make-worker-thread)))

  (for ([thd (in-list threads)])
    (async-channel-put thread-pool thd))

  (define timer-ch (make-async-channel))
  (define timer-mgr (make-reactor timer-ch))

  (define we (make-will-executor))
  (define wt (thread (lambda () (let loop () (will-execute we) (loop)))))

  (runtime (runtime-loop) thread-pool work-queue threads timer-mgr timer-ch
           we wt
           (box 0) (make-semaphore 1) (make-semaphore 0)))


(define (startup)
  (set-box! *runtime* (make-runtime)))


(define (shutdown)
  (define rt (assert-runtime))
  (set-box! *runtime* #f)
  (kill-thread (runtime-main rt))
  (kill-thread (runtime-reactor rt))
  (kill-thread (runtime-will-thread rt))
  (for ([thd (in-list (runtime-threads rt))])
    (kill-thread thd)))


(define (block-on entry-value)
  (define task
    (cond
      [(coroutine? entry-value)
       (define t (make-pending-task #f))
       (schedule-resume! t entry-value)
       t]
      [(task? entry-value) entry-value]
      [else (error "block-on: expected coroutine or task")]))
  (define sem (make-semaphore 0))
  (on-completed! (get-awaiter task)
                 (lambda (_) (semaphore-post sem)))
  (semaphore-wait sem)
  (collect-garbage)
  (unless (eq? (*destruction*) 'terminated)
    (define rt (unbox *runtime*))
    (when rt
      (let loop ()
        (define count
          (call-with-semaphore (runtime-pending-lock rt)
            (lambda () (unbox (runtime-pending-count rt)))))
        (when (> count 0)
          (semaphore-wait (runtime-all-settled rt))
          (loop)))))
  (get-result task))

(define-syntax (block stx)
  (syntax-parse stx
    [(_ entry:id)
     #'(dynamic-wind startup
                     (lambda () (block-on (entry)))
                     shutdown)]))


;; ============
;; CANCELLATION
;; ============


(define (add-cancel-callback! t cb)
  (with-task-lock t
    (if (task-cancelled? t)
        (cb)
        (set-task-cancel-callbacks! t (cons cb (task-cancel-callbacks t))))))

;; Requires: awareness != #f.
;; Pure marking — the scheduler and reactor enforce cancellation.
;; Marking is always top-down; the observable cancellation direction emerges
;; from the await structure (leaves are resumed before parents because
;; parents are suspended awaiting children).
(define (cancel! t)
  (when (and (task? t) (not (settled? t)))
    (set-task-cancelled?! t #t)
    (for ([cb (task-cancel-callbacks t)])
      (cb))
    (set-task-cancel-callbacks! t '())
    (when (eq? (*extent*) 'dynamic)
      (for ([child (task-children t)])
        (cancel! child)))))


;; ======
;; SYNTAX
;; ======


(define-syntax-parameter await
  (lambda (stx)
    (raise-syntax-error
     'await "await can only be used inside of an async function" stx)))


(define (resume! task coro resume-value)
  (parameterize ([*current-task* task])
    (with-handlers
        ([exn:userland? (lambda (e) (task-settled! task e #:failed? #t))])
      (define body-thunk ((coroutine-activate coro) resume-value))
      (define result (reset (body-thunk)))
      (cond
        [(suspended? result)
         (define task-ref (hold-task task))
         (on-completed! (suspended-awaiter result)
                        (lambda (_)
                          (define t (deref-task task-ref))
                          (when t
                            (schedule-resume! t (suspended-coro result)))))]
        [else
         (task-settled! task result)]))))


(define-syntax-rule (await-impl expr-to-await)
  (let loop ([v expr-to-await])
    (cond
      ;; splice coroutine frame
      [(coroutine? v)
       (let ([result (((coroutine-activate v) '()))])
         (if (or (coroutine? result) (awaitable? result))
             (loop result)
             result))]

      [(not (awaitable? v))
       (raise-argument-error 'await "value not awaitable?" v)]

      ;; continue immediately
      [(and (is-completed? (get-awaiter v))
            (eq? (*suspension*) 'dynamic))
       (get-result (get-awaiter v))]

      ;; suspend
      [else
       (define awaiter (get-awaiter v))
       (shift k
              (suspended awaiter
                         (coroutine
                          (lambda (resume)
                            (assert-resume! resume)
                            (lambda () (k (get-result awaiter)))))))])))

(define-syntax-rule (lambda/async (arg ...) body ...)
  (lambda (arg ...)
    (define (main-body-thunk)
      (syntax-parameterize ([await (make-rename-transformer #'await-impl)]
                            [is-cancelled? (make-rename-transformer #'is-cancelled?-impl)]
                            [cancel (make-rename-transformer #'cancel-impl)])
        (begin body ...)))
    (define coro (coroutine
                  (lambda (_resume)
                    main-body-thunk)))
    (case (*eagerness*)
      [(eager)
       (define return-task (make-pending-task (*current-task*)))

       (resume! return-task coro '())
       return-task]
      [(semi-eager)
       (define return-task (make-pending-task (*current-task*)))

       (schedule-resume! return-task coro)
       return-task]
      [(lazy) coro])))


(define-syntax-rule (define/async (name arg ...) body ...)
  (define name (lambda/async (arg ...) body ...)))


;; =====
;; SPAWN
;; =====


(define (spawn thing)
  (define parent (*current-task*))
  (cond
    [(coroutine? thing)
     (define new-task (make-pending-task parent))
     (schedule-resume! new-task thing)
     new-task]
    [(task? thing) thing]
    [else (raise-argument-error 'spawn "coroutine? or task?" thing)]))


;; ============
;; IO / REACTOR
;; ============

;; A promise is a lightweight one-shot awaitable. Not a task — no parent/child,
;; no cancellation state, no will executor. Just a box that gets fulfilled once,
;; triggering callbacks.
(struct promise (completed? value callbacks mutex)
  #:mutable

  #:methods gen:awaitable
  [ (define (get-awaiter p) p) ]

  #:methods gen:awaiter
  [ (define (is-completed? p) (promise-completed? p))

    (define (on-completed! p k)
      (call-with-semaphore (promise-mutex p)
                           (lambda ()
                             (cond
                               [(promise-completed? p) (k p)]
                               [else
                                (set-promise-callbacks! p (cons k (promise-callbacks p)))]))))

    (define (get-result p) (promise-value p)) ])

(define (make-promise)
  (promise #f (void) '() (make-semaphore 1)))

(define (fulfil! p v)
  (call-with-semaphore (promise-mutex p)
                       (lambda ()
                         (unless (promise-completed? p)
                           (set-promise-completed?! p #t)
                           (set-promise-value! p v)
                           (for ([k (reverse (promise-callbacks p))])
                             (k p))
                           (set-promise-callbacks! p '())))))


;; Timer registration: deadline, promise to fulfil, value, and cancel semaphore.
(struct timer-reg (deadline promise value cancel-sema))

(define (insert-timer reg timers)
  (cond
    [(null? timers) (list reg)]
    [(<= (timer-reg-deadline reg) (timer-reg-deadline (car timers)))
     (cons reg timers)]
    [else (cons (car timers) (insert-timer reg (cdr timers)))]))

;; The reactor watches three kinds of events:
;;   1. New timer registrations (via channel)
;;   2. Timer deadlines (via alarm-evt)
;;   3. Cancellation signals (via per-timer semaphores)
;; Whichever fires first wins.
(define (make-reactor timer-channel)
  (thread
   (lambda ()
     (let loop ([timers '()])
       (define reg-evt
         (wrap-evt timer-channel (lambda (r) (list 'register r))))
       (define cancel-evts
         (for/list ([r timers])
           (wrap-evt (timer-reg-cancel-sema r)
                     (lambda (_) (list 'cancel r)))))
       (define alarm-evts
         (if (null? timers) '()
             (list (wrap-evt (alarm-evt (timer-reg-deadline (car timers)))
                             (lambda (_) (list 'alarm))))))
       (define result (apply sync (cons reg-evt (append alarm-evts cancel-evts))))
       (case (car result)
         [(register)
          (loop (insert-timer (cadr result) timers))]
         [(cancel)
          (define cancelled-reg (cadr result))
          (fulfil! (timer-reg-promise cancelled-reg) (void))
          (loop (filter (lambda (r) (not (eq? r cancelled-reg))) timers))]
         [(alarm)
          (define now (current-inexact-milliseconds))
          (define-values (expired remaining)
            (partition (lambda (r) (<= (timer-reg-deadline r) now)) timers))
          (for ([r expired])
            (fulfil! (timer-reg-promise r) (timer-reg-value r)))
          (loop remaining)])))))


(define/async (io/delay ms [v (void)])
  (define p (make-promise))
  (define sema (make-semaphore))
  (define deadline (+ (current-inexact-milliseconds) ms))
  (async-channel-put (runtime-timer-channel (unbox *runtime*))
                     (timer-reg deadline p v sema))
  (add-cancel-callback! (*current-task*)
                        (lambda () (semaphore-post sema)))
  (await p))
