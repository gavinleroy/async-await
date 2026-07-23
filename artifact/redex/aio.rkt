#lang racket/base

(require redex/reduction-semantics
         (only-in racket/list flatten)
         "core.rkt"
         "py.rkt"
         "platform.rkt")

(provide AsyncIO -->aio -->>aio)

(define-extended-ev-system AsyncIO
  #:def-reduction -->sys
  #:def-exn-reduction -->sys/exn
  #:with-base-lang Py
  #:with-base-reduction -->py
  #:single-threaded
  ;; No #:serial-dispatch: run-to-completion is structural -- ready thunks run
  ;; as frames stacked on the root thread (see sys/schedule below), so nothing
  ;; can dispatch while a callback is mid-run. And asyncio has no
  ;; micro-before-macro priority: call_soon callbacks and due timer callbacks
  ;; feed the same FIFO ready deque, so sys/signal must NOT wait for an idle
  ;; loop (a due timer is queued while an earlier callback still runs).
  (e ::= .... (spawn e) (cancel e))
  (E ::= .... (spawn E) (cancel E))
  (M ::= .... (spawn M) (cancel M))
  (G ::= .... (spawn G) (cancel G)))

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->aio/core
  (reduction-relation
   AsyncIO
   #:domain (t σ Q T P)

   ;; EAGERNESS: lazy, a coroutine comes from the Py model when an async/lambda is applied
   [--> (t_0 σ_0 Q_0 T (FS_0 ... (thread (label (in-hole E (spawn v_coro))) F ...) FS_1 ...))
        (t_1 σ_2 Q_1 T (FS_0 ... (thread (label (in-hole E x_task)) F ...) FS_1 ...))

        (where/error (σ_1 x_task v_task) (task:allocate σ_0))
        (where/error σ_2 (ext1 σ_1 (x_task v_task)))
        (where/error Q_1 (Q:push Q_0
                                 (x_task
                                  (lambda (none)
                                    (reset
                                     (begin
                                       (catch (lambda (v_err) (task:set-failed! x_task v_err))
                                              (begin none (task:set-done! x_task (await v_coro))))
                                       (os/start-soon (task:get-dependents x_task))))
                                    ;; EXTENT: indefinite, at the end of the task scope we don't destroy
                                    ;; tasks that were spawned during the execution of `v_coro`.
                                    ))))
        (where/error t_1 t_0)
        "spawn"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (await v_awaitable))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ...
                    (thread (label (in-hole E
                                            (begin
                                              (task:set-awaited! v_awaitable)
                                              ;; SUSPENSION: dynamic, if the value is ready no need to suspend
                                              (if (task:is-completed? v_awaitable)
                                                  (task:get-result v_awaitable)
                                                  (shift k
                                                         (task:add-self-as-dependent!
                                                          v_awaitable
                                                          (label (task:continue-with v_awaitable k)))))))) F ...) FS_1 ...))

        (where #true (task:is-task? v_awaitable))
        (where/error t_1 t_0)
        "await-task"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (cancel v_task))) F ...) FS_1 ...))
        (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (task:set-cancelled! v_task))) F ...) FS_1 ...))
        "cancel"]

   ;; The entry coroutine: asyncio.run wraps it in a task and the ONE thread
   ;; immediately starts driving it -- run_until_complete never returns to the
   ;; scheduler first, so anything already in Q runs strictly after main's
   ;; first suspension. Modeled by stacking the task's wrapper frame directly
   ;; on the root thread (contrast spawn, which pushes to the BACK of Q). No
   ;; (begin none ...) first-run hook here: nothing can cancel the entry task
   ;; before its first step.
   [--> (t_0 σ_0 Q T ((thread (root (in-hole E (os/block (name v_coro (lambda (x) e)))))) FS ...))
        (t_1 σ_2 Q T ((thread (x_task (reset
                                       (begin
                                         (catch (lambda (v_err) (task:set-failed! x_task v_err))
                                                (task:set-done! x_task (await v_coro)))
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
   AsyncIO

   ;; SINGLE-THREADED: the event loop IS the root thread. run_until_complete
   ;; executes ready callbacks on the calling thread, so dispatch (these two
   ;; rules shadow the platform's, which require an empty worker slot) pops the
   ;; ready queue and runs the thunk as a frame stacked on the parked root.
   ;; The pattern is the idle gate: while a callback frame sits on top of
   ;; root, or before os/block-coro has started the entry task (is-task?
   ;; fails on the coroutine), neither rule can fire.
   [-->
    (t_0 σ Q_0 T ((thread (root (in-hole E (os/block v_task)))) FS ...))
    (t_1 σ Q_1 T ((thread (label_waiting (v_thunk (void)))
                          (root (in-hole E (os/block v_task))))
                  FS ...))

    (where #true (task:is-task? v_task))
    (where ((label_waiting v_thunk) Q_1) (Q:pop Q_0))
    (where #false (task:cancelled? σ label_waiting))
    (where/error t_1 t_0)
    "sys/schedule"]

   ;; Cancelled-task dispatch keeps AsyncIO's one-shot delivery: throw the
   ;; cancellation into the thunk and uncancel (the flag is consumed).
   [-->
    (t_0 σ_0 Q_0 T ((thread (root (in-hole E (os/block v_task)))) FS ...))
    (t_1 σ_1 Q_1 T ((thread (label_waiting (throw-in v_thunk "cancelled"))
                            (root (in-hole E (os/block v_task))))
                    FS ...))

    (where #true (task:is-task? v_task))
    (where ((label_waiting v_thunk) Q_1) (Q:pop Q_0))
    (where #true (task:cancelled? σ_0 label_waiting))
    (where/error σ_1 (task:uncancel σ_0 label_waiting))
    (where/error t_1 t_0)
    "sys/schedule-cancelled"]

   ;; STRENGTH weak, `Q`, the Executor loop is not a part of the GC root set
   [--> (t_0 (any_before ... (x v) any_after ...) (any_0 ... (x _) any_1 ...) T PS)
        (t_1 (any_before ... any_after ...) (any_0 ... any_1 ...) T PS)
        (side-condition
         (let ([remaining-state (term (T PS any_before ... any_after ...))])
           (not (memq (term x) (flatten remaining-state)))))
        (where/error t_1 t_0)
        "sys/gc"]


   [--> (t_0 σ Q T ((thread (root (in-hole E (os/block v_task)))) FS ...))
        (t_1 σ Q T ((thread (root (in-hole E (begin
                                               (cancel x_0 x_1 ...)
                                               (os/block v_task))))) FS ...))

        (where #true (task:settled? σ v_task))
        (where (x_0 x_1 ...) (store:get-uncancelled-tasks σ))
        (where/error t_1 t_0)
        "os/block-cancel"]

   ;; PROPAGATION: log. asyncio.run returns the entry task's value; an
   ;; exception in a task that was never awaited does NOT propagate into user
   ;; code -- the loop reports it out-of-band ("Task exception was never
   ;; retrieved", on stderr), a channel outside the model's observables.
   ;; Equivalently: a reraise caught immediately at the runtime boundary. If
   ;; main itself failed, task:get-result rethrows its error, which IS what
   ;; asyncio.run does.
   [--> (t_0 σ () () ((thread (root (in-hole E (os/block v_task)))) FS ...))
        (t_1 σ () () ((thread (root (in-hole E (task:get-result v_task)))) FS ...))

        (where #true (task:settled? σ v_task))
        (where () (store:get-uncancelled-tasks σ))
        (where/error t_1 t_0)
        "os/block-exit"]))

(define -->aio
  (union-reduction-relations
   (make-big-step -->sys/overriden)
   -->aio/core))

;; Non-collapsing variant that exposes every successor (drops the make-big-step
;; wrapper). Drives whole-state-space exploration: the directed witness search
;; (fuzz/witness.rkt) and the reference enumerator (fuzz/reference.rkt).
(define -->>aio
  (union-reduction-relations
   -->sys/overriden
   -->aio/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (prefix-in unit: rackunit)
           (submod "core.rkt" niceties)
           "utils.rkt"
           "fuzz/check.rkt"
           "fuzz/run.rkt")

  ;; #:threads 1: the model runs asyncio on a single P-slot (the root thread
  ;; is the event loop), matching the single-threaded runtime.
  (define-syntax-rule (aio-->>= e v)
    (begin
      (test-->> -->aio #:equiv prog/equiv (async/main #:threads 1 e) v)
      (check-runtime-output compile-and-run-asyncio 'e v)))

  (define-syntax-rule (aio-->>∈ e results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->aio (async/main #:threads 1 e) results
                             #:iterations 5
                             #:extract-result program-output)))
      (check-runtime-in-set compile-and-run-asyncio 'e results))))

(module+ test
  (aio-->>=
   (os/block ((async/lambda (x) x) 42))
   42)

  (aio-->>=
   (trace-stdout (print)
     (let* ([suspend (async/lambda () (void))]
            [work (async/lambda (msg)
                    (begin (await (suspend))
                           (print msg)))]
            [c (work "A")])
       (os/block c)))
   "A")

  (aio-->>=
   (let* ([work (async/lambda ()
                  (await (os/io 1 42)))])
     (os/block (work)))
   42)

  (aio-->>=
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))])
     (os/block (work)))
   42)

  (aio-->>=
   (let* ([work (async/lambda ()
                  (begin (await (os/io 1 (void)))
                         (await (os/io 1 (void)))
                         42))]
          [main (async/lambda () (await (spawn (work))))])
     (os/block (main)))
   42)

  ;; PROPAGATION: log -- an unretrieved task exception never reaches user
  ;; code (the root catch stays empty) and asyncio.run returns main's value.
  ;; The loop's "Task exception was never retrieved" report is stderr-only,
  ;; outside the model's observables.
  (aio-->>=
   (let* ([exn (async/lambda ()
                 (throw "whoops"))]
          [main (async/lambda ()
                  (let ([t (spawn (exn))])
                    (await (os/io 1 42))))])
     (catch (lambda (e) e)
            (os/block (main))))
   42)

  (aio-->>=
   (trace-stdout (print)
     (let* ([append-it (async/lambda () (print "A"))]
            [transparent (async/lambda ()
                           (let ([ret (append-it)])
                             (begin (print "B") ret)))])
       (os/block (transparent))))
   "B")

  (aio-->>∈
   (let* ([work (async/lambda () (await (os/io 20 0)))]
          [main (async/lambda ()
                  (let ([t (spawn (work))])
                    (begin
                      (cancel t)
                      (await t))))])
     (catch (lambda (e) "cancelled")
            (os/block (main))))
   '("cancelled" 0))

  (aio-->>=
   (let* ([mk-t1 (async/lambda () (throw 42))]
          [mk-t2 (async/lambda (x)
                   (catch (lambda (v) v)
                          (begin
                            (await (mk-t1))
                            x)))])

     (os/block (mk-t2 0)))
   42)

  (aio-->>∈
   (let* ([f0 (async/lambda () (await (os/io 1000000 0)))]
          [f1 (async/lambda () (await (spawn (f0))))]
          [f2 (async/lambda () (await (spawn (f1))))]
          [main (async/lambda ()
                  (catch (lambda (e) "cancelled")
                         (let ([t (spawn (f2))])
                           (begin
                             (await (os/io 1 (void)))
                             (cancel t)
                             (await t)))))])
     (os/block (main)))
   '("cancelled"))

  ;; The task is cancelled before its first step (main runs inline ahead of
  ;; anything create_task queued), so the cancellation is raised at the
  ;; coroutine's entry: work's catch never engages and 42 is unreachable.
  ;; Matches real asyncio, which raises CancelledError out of asyncio.run.
  (aio-->>∈
   (let* ([work (async/lambda ()
                  (catch (lambda (e) 42)
                         (await (os/io 10 0))))]
          [t (spawn (work))]
          [main (async/lambda ()
                  (begin (cancel t)
                         (await t)))])
     (catch (lambda (e) "cancelled")
            (os/block (main))))
   '("cancelled"))

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
       (os/block (main))))
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
       (os/block (main))))
   ; 'C' must *always* come before 'A'
   (filter (lambda (s) (before s #\C #\A))
           (string-permutations "ABC"))))
