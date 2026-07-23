#lang racket/base

(require redex/reduction-semantics
         (only-in racket/list flatten)
         "core.rkt"
         "py.rkt"
         "platform.rkt")

(provide Trio -->trio -->>trio)

(define-extended-ev-system Trio
  #:def-reduction -->sys
  #:def-exn-reduction -->sys/exn
  #:with-base-lang Py
  #:with-base-reduction -->py
  #:single-threaded
  (e ::= .... (spawn e) (cancel e))
  (E ::= .... (spawn E) (cancel E))
  (M ::= .... (spawn M) (cancel M))
  (G ::= .... (spawn G) (cancel G)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->trio/core
  (reduction-relation
   Trio
   #:domain (t σ Q T P)

   ;; EAGERNESS: lazy, a coroutine comes from the Py model when an async/lambda is applied
   [--> (t_0 σ_0 Q_0 T (FS_0 ... (thread (label (in-hole E (spawn v_coro))) F ...) FS_1 ...))
        (t_1 σ_2 Q_1 T (FS_0 ... (thread (label (in-hole E x_task)) F ...) FS_1 ...))

        (where/error (σ_1 x_task v_task) (task:allocate-dependency σ_0 label))
        (where/error σ_2 (ext1 σ_1 (x_task v_task)))
        (where/error Q_1 (Q:push Q_0
                                 (x_task
                                  (lambda (none)
                                    (reset
                                     (begin
                                       (catch (lambda (v_err) (task:set-failed! x_task v_err))
                                              (begin none (task:set-done! x_task (await v_coro))
                                                     ;; DESTRUCTION: awaited, tasks aren't cancelled here!
                                                     ;; EXTENT: dynamic, at the end of the task scope we don't destroy
                                                     ;; tasks that were spawned during the execution of `v_coro`.
                                                     (task:await-dependencies x_task)))
                                       (os/start-soon (task:get-dependents x_task))))
                                    ))))
        (where/error t_1 t_0)
        "spawn"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (await v_awaitable))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ...
                    (thread (label (in-hole E
                                            ;; SUSPENSION: dynamic, if the value is ready no need to suspend
                                            (if (task:is-completed? v_awaitable)
                                                (task:get-result v_awaitable)
                                                (shift k
                                                       (task:add-self-as-dependent!
                                                        v_awaitable
                                                        (label (task:continue-with v_awaitable k))))))) F ...) FS_1 ...))

        (where #true (task:is-task? v_awaitable))
        (where/error t_1 t_0)
        "await-task"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (cancel v_task))) F ...) FS_1 ...))
        (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (task:set-cancelled! v_task))) F ...) FS_1 ...))

        "cancel"]

   ;; The entry coroutine: trio.run starts the initial task immediately on the
   ;; calling thread -- nothing queued by the root prefix runs until main's
   ;; first checkpoint. Modeled by stacking the entry task's wrapper frame
   ;; directly on the root thread (contrast spawn, which pushes to the BACK of
   ;; Q). Same wrapper as spawn's thunk -- including the await-dependencies
   ;; tail (the entry function's implicit nursery) -- minus the (begin none
   ;; ...) first-run hook: nothing can cancel the entry task before its first
   ;; step.
   [--> (t_0 σ_0 Q T ((thread (root (in-hole E (os/block (name v_coro (lambda (x) e)))))) FS ...))
        (t_1 σ_2 Q T ((thread (x_task (reset
                                       (begin
                                         (catch (lambda (v_err) (task:set-failed! x_task v_err))
                                                (begin (task:set-done! x_task (await v_coro))
                                                       (task:await-dependencies x_task)))
                                         (os/start-soon (task:get-dependents x_task)))))
                              (root (in-hole E (os/block x_task))))
                      FS ...))

        (where/error (σ_1 x_task v_task) (task:allocate σ_0))
        (where/error σ_2 (ext1 σ_1 (x_task v_task)))
        (where/error t_1 t_0)
        "os/block-coro"]))

(define -->sys/overriden
  (extend-reduction-relation
   -->sys/exn
   Trio

   ;; SINGLE-THREADED: the scheduler IS the root thread (trio.run executes
   ;; tasks on the calling thread). These shadow the platform dispatch rules,
   ;; which require an empty worker slot: the next ready thunk runs as a frame
   ;; stacked on the parked root, so run-to-completion is structural.
   ;;
   ;; ANY-ORDER DISPATCH: trio's scheduler is deliberately nondeterministic --
   ;; it shuffles each batch of runnable tasks (spawn-start order and
   ;; same-deadline wakeups both vary run to run). Modeled by popping an
   ;; ARBITRARY ready thunk, not the queue head; this over-approximates the
   ;; batch structure, which is the sound direction for the membership oracle.
   [-->
    (t_0 σ (any_qpre ... (label_waiting v_thunk) any_qpost ...) T
         ((thread (root (in-hole E (os/block v_task)))) FS ...))
    (t_1 σ (any_qpre ... any_qpost ...) T
         ((thread (label_waiting (v_thunk (void)))
                  (root (in-hole E (os/block v_task))))
          FS ...))

    (where #true (task:is-task? v_task))
    (where #false (task:cancelled? σ label_waiting))
    (where/error t_1 t_0)
    "sys/schedule"]

   ;; A cancelled task that has NEVER run dispatches normally: trio guarantees
   ;; a start_soon'd child runs until its first checkpoint even if its scope
   ;; was cancelled first (probed: the sync prefix prints; a child with no
   ;; checkpoint runs to successful completion). Delivery at that first
   ;; checkpoint needs no extra rules -- the task's first await registers an
   ;; io/task child, the cancelled-timer pull (sys/signal-cancel) fires, and
   ;; the wake path below throws at the await. Fresh spawn thunks are exactly
   ;; the reset-shaped ones (spawn pushes (lambda (none) (reset ...)));
   ;; resumed continuations are catch-shaped, io wakeups begin-shaped.
   [-->
    (t_0 σ (any_qpre ... (label_waiting (name v_thunk (lambda (x_arg) (reset e_body)))) any_qpost ...) T
         ((thread (root (in-hole E (os/block v_task)))) FS ...))
    (t_1 σ (any_qpre ... any_qpost ...) T
         ((thread (label_waiting (v_thunk (void)))
                  (root (in-hole E (os/block v_task))))
          FS ...))

    (where #true (task:is-task? v_task))
    (where #true (task:cancelled? σ label_waiting))
    (where/error t_1 t_0)
    "sys/schedule-cancelled-fresh"]

   ;; A cancelled task being RESUMED was suspended at an await -- a
   ;; checkpoint -- so throwing into the continuation IS trio's
   ;; deliver-at-checkpoint. Sticky scopes: no task:uncancel (contrast
   ;; asyncio's one-shot delivery).
   [-->
    (t_0 σ (any_qpre ... (label_waiting v_thunk) any_qpost ...) T
         ((thread (root (in-hole E (os/block v_task)))) FS ...))
    (t_1 σ (any_qpre ... any_qpost ...) T
         ((thread (label_waiting (throw-in v_thunk "cancelled"))
                  (root (in-hole E (os/block v_task))))
          FS ...))

    (where #true (task:is-task? v_task))
    (where #true (task:cancelled? σ label_waiting))
    (side-condition (not (redex-match? Trio (lambda (x) (reset e)) (term v_thunk))))
    (where/error t_1 t_0)
    "sys/schedule-cancelled"]

   ;; Override of the platform os/io: allocate the io task as a CHILD of the
   ;; issuing task (allocate-dependency) so cancel scopes reach pending io.
   ;; The catch wrapper mirrors the platform's exn variant -- without it a
   ;; cancellation thrown into the thunk (sys/schedule-cancelled) escapes as
   ;; a bare throw, wedging the thread, and the io task never records
   ;; "failed", so its waiters are never woken.
   [--> (t_0 σ_0 Q T (FS_0 ... (thread (label (in-hole E (os/io t v))) F ...) FS_1 ...))
        (t_1 σ_2 Q T (FS_0 ...
                      (thread (x_io (os/start-later (+ (os/time) t)
                                                    x_io
                                                    (lambda (none)
                                                      (begin
                                                        (catch (lambda (e) (task:set-failed! x_io e))
                                                               (begin
                                                                 none
                                                                 (task:set-done! x_io v)))
                                                        (os/start-soon (task:get-dependents x_io))))))
                              (label (in-hole E x_io)) F ...) FS_1 ...))

        (where/error (σ_1 x_io v_task) (task:allocate-dependency σ_0 label))
        (where/error σ_2 (ext1 σ_1 (x_io v_task)))
        (where/error t_1 t_0)
        "os/io"]

   [--> (t_0 σ Q T ((thread (root (in-hole E (os/block v_task)))) FS ...))
        (t_1 σ Q T ((thread (root (in-hole E (begin
                                               (cancel x_0 x_1 ...)
                                               (os/block v_task))))) FS ...))

        (where #true (task:settled? σ v_task))
        (where (x_0 x_1 ...) (store:get-uncancelled-tasks σ))
        (where/error t_1 t_0)
        "os/block-cancel"]

   [--> (t_0 σ () () ((thread (root (in-hole E (os/block v_task)))) FS ...))
        (t_1 σ () () ((thread (root (in-hole E (task:get-result v_task)))) FS ...))

        (where #true (task:settled? σ v_task))
        (where () (store:get-uncancelled-tasks σ))
        (where none (store:find-unawaited-error σ))
        (where/error t_1 t_0)
        "os/block-exit"]))

(define -->trio
  (union-reduction-relations
   (make-big-step -->sys/overriden)
   -->trio/core))

;; Non-collapsing variant that exposes every successor (drops the make-big-step
;; wrapper). Drives whole-state-space exploration: the directed witness search
;; (fuzz/witness.rkt) and the reference enumerator (fuzz/reference.rkt).
(define -->>trio
  (union-reduction-relations
   -->sys/overriden
   -->trio/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (prefix-in unit: rackunit)
           (submod "core.rkt" niceties)
           "utils.rkt"
           "fuzz/check.rkt"
           "fuzz/run.rkt")

  ;; #:threads 1: the model runs trio on a single P-slot (the root thread is
  ;; the scheduler), matching the single-threaded runtime.
  (define-syntax-rule (trio-->>= e v)
    (begin
      (test-->> -->trio #:equiv prog/equiv (async/main #:threads 1 e) v)
      (check-runtime-output compile-and-run-trio 'e v)))

  (define-syntax-rule (trio-->>∈ e results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->trio (async/main #:threads 1 e) results
                             #:iterations 5
                             #:extract-result program-output)))
      (check-runtime-in-set compile-and-run-trio 'e results))))

(module+ test
  (trio-->>=
   (os/block ((async/lambda () 42)))
   42)

  (trio-->>=
   (os/block ((async/lambda (x) x) 42))
   42)

  (trio-->>=
   (let* ([yield (async/lambda () (void))]
          [id (async/lambda (x)
                (begin
                  (await (yield))
                  x))])

     (os/block (id 42)))
   42)

  (trio-->>=
   (let* ([mk-t1 (async/lambda () (throw 42))]
          [mk-t2 (async/lambda (x)
                   (catch (lambda (v) v)
                          (begin
                            (await (mk-t1))
                            x)))])

     (os/block (mk-t2 0)))
   42)

  (trio-->>=
   (let ([work (async/lambda () (await (os/io 5 42)))])
     (os/block (work)))
   42)

  (trio-->>=
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (begin
                      (print (await (os/io 1 msg)))
                      (print (await (os/io 1 msg)))))])
       (os/block (work "A"))))
   "AA")

  ;; The recursive loops below are async/lambdas: `await` inside a sync
  ;; lambda emits `await` in a sync Python def -- a SyntaxError. Awaiting the
  ;; recursive call is semantically neutral in both the model and Python
  ;; (awaiting a bare coroutine drives it inline; not a checkpoint).
  (trio-->>∈
   (trace-stdout (print)
     (let* ([worker (async/lambda ()
                      (letrec ([loop (async/lambda (i)
                                       (when (< i 3)
                                         (begin
                                           (await (os/io 1 (print "A")))
                                           (await (loop (+ 1 i))))))])
                        (await (loop 0))))]
            [main (async/lambda ()
                    (let ([w (spawn (worker))])
                      (begin (await (os/io 1 (void)))
                             (cancel w)
                             (catch (lambda (e) (print "C"))
                                    (await w)))))])
       (os/block (main))))
   '("C" "AC" "AAC" "AAAC" "AAA"))

  ;; `msg` is threaded through `loop` as a parameter: the python emitter
  ;; hoists lambdas to module-level defs, so a lambda closing over an
  ;; enclosing function's parameter loses it (NameError at runtime).
  (trio-->>∈
   (trace-stdout (print)
     (let* ([get-truth (async/lambda () #true)]
            [work (async/lambda (msg)
                    (letrec ([loop (async/lambda (msg i)
                                     (when (< i 3)
                                       (begin
                                         (when (await (get-truth))
                                           (print msg))
                                         (await (loop msg (+ 1 i))))))])
                      (await (loop msg 0))))]
            [main (async/lambda ()
                    (let ([task0 (work "A")]
                          [task1 (work "B")])
                      (begin (print "C")
                             (await task0)
                             (await task1))))])
       (os/block (main))))
   (map (lambda (s) (string-append "C" s))
        (string-permutations "AAABBB")))

  (trio-->>∈
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
       (os/block (main))))
   (string-permutations "ABC")))
