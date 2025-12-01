#lang racket

;; TODO: C# uses a queue per task. A child task
;; inherits the same thread as its parent.

(require racket/generic
         racket/stxparam
         racket/control
         racket/async-channel)


(provide define/async
         await
         *pool-size*
         async-run-entry
         delay)

;; =========
;; ECOSYSTEM
;; =========

(define-generics awaitable
  (get-awaiter awaitable))


(define-generics awaiter
  (is-completed? awaiter)
  (on-completed! awaiter k)
  (get-result awaiter))


(struct task (state value callbacks)
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
        [(pending? t) (raise "ICE: task is still running")]
        [(failed? t) (raise (task-value t))]
        [(completed? t) (task-value t)])) ])


(define (make-pending-task) (task 'pending #f '()))
(define (pending? t) (eq? (task-state t) 'pending))
(define (completed? t) (eq? (task-state t) 'completed))
(define (failed? t) (eq? (task-state t) 'failed))
(define (settled? t) (not (pending? t)))


(define (task-settled! t v #:failed? [failed? #false])
  (when (pending? t)
    (define status (if failed? 'failed 'completed))
    (set-task-state! t status)
    (set-task-value! t v)
    (for ([callback (reverse (task-callbacks t))])
      (callback t))
    (set-task-callbacks! t '())))


(define (task-on-complete! t callback)
  (cond
    [(settled? t) (callback t)]
    [(pending? t)
     (set-task-callbacks! t (cons callback (task-callbacks t)))]))


;; =======
;; RUNTIME
;; =======


(define *runtime* (box #f))


(struct runtime (main thread-pool work-queue threads))


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

(define (wait-for-work!)
  (async-channel-get (runtime-work-queue (assert-runtime))))

(define (schedule-work! thnk)
  (async-channel-put (runtime-work-queue (assert-runtime))
                     thnk))


(define (runtime-loop)
  (thread
   (lambda ()
     (let loop ([thunk (wait-for-work!)]
                [thd (wait-for-thread!)])
       (thread-send thd
                    (lambda ()
                      (thunk)
                      (release-thread! thd)))
       (loop (wait-for-work!)
             (wait-for-thread!))))))


(define (make-worker-thread)
  (thread
   (lambda ()
     (let loop ([thunk (thread-receive)])
       (with-handlers ([(lambda (_) #t)
                        (lambda (e)
                          (printf "Worker thread caught exception: ~a\n" e))])
         (thunk))
       (loop (thread-receive))))))

(define *pool-size* (make-parameter 8))

(define (make-runtime)
  (define n-threads (*pool-size*))
  (define work-queue (make-async-channel))
  (define thread-pool (make-async-channel n-threads))
  (define threads
    (for/list ([_ (in-range n-threads)])
      (make-worker-thread)))

  (for ([thd (in-list threads)])
    (async-channel-put thread-pool thd))

  (runtime (runtime-loop) thread-pool work-queue threads))


(define (startup)
  (set-box! *runtime* (make-runtime)))


;; DESIGN DECISIONS:
;; 1. What if there is work in the queue?
;; 2. What if the threads are busy?
;;
;; This implementation terminates everything,
;; immediately, and all pending work is destroyed.
(define (shutdown)
  (define rt (assert-runtime))
  ;; Make runtime inaccessible
  (set-box! *runtime* #f)
  (kill-thread (runtime-main rt))
  (for ([thd (in-list (runtime-threads rt))])
    (kill-thread thd)))


(define (block-on awaitable)
  (define return (void))
  (define wait-sem (make-semaphore 0))
  (define awaiter (get-awaiter awaitable))
  (on-completed! awaiter
                 (lambda (awaitable)
                   (set! return awaitable)
                   (semaphore-post wait-sem)))
  (semaphore-wait wait-sem)
  (get-result awaitable))


(define-syntax-rule (async-run-entry entry)
  (dynamic-wind
   startup (lambda () (block-on (entry))) shutdown))


;; ======
;; SYNTAX
;; ======


(define-syntax-parameter await
  (lambda (stx)
    (raise-syntax-error
     'await "await can only be used inside of an async function" stx)))


(define async-prompt (make-continuation-prompt-tag))


(define (run-computation return-task thunk)
  (call/prompt
   (lambda ()
     (with-handlers ([(lambda (_) #t)
                      (lambda (e) (task-settled! task e #:failed? #t))])
       (define result (thunk))
       (task-settled! return-task result)))
   async-prompt
   (lambda (awaitable k)
     (define awaiter (get-awaiter awaitable))
     ;; DESIGN DECISION:
     ;; 1. Continue if the result is ready
     ;; 2. This was an await point, so schedule the work in the queue
     (if (is-completed? awaiter)
         (k (get-result awaiter))
         (on-completed!
          awaiter
          (lambda (awaiter)
            (schedule-work!
             (lambda ()
               (k (get-result awaiter))))))))))


(define-syntax-rule (await-impl expr-to-await)
  (call/cc
   (lambda (k)
     (abort/cc async-prompt expr-to-await k))))

(define-syntax-rule (lambda/async (arg ...) body ...)
  (lambda (arg ...)
    (define return-task (make-pending-task))
    (define (main-body-thunk)
      (syntax-parameterize ([await (make-rename-transformer #'await-impl)])
        (begin body ...)))
    ;; DESIGN DECISION:
    ;; 1. Run this immediately on *this* thread
    ;; 2. Schedule the work in the queue
    (run-computation return-task main-body-thunk)
    return-task))


(define-syntax-rule (define/async (name arg ...) body ...)
  (define name (lambda/async (arg ...) body ...)))


;; ==========
;; PRIMITIVES
;; ==========


(define (delay ms [v (void)])
  (define t (make-pending-task))
  (schedule-work!
   (lambda ()
     (sleep (/ ms 1000)) ; sleep takes seconds
     (task-settled! t v)))
  t)


(module+ test
  (require rackunit)
  (define (run-tests)
    (void)
    )

  (run-tests))
