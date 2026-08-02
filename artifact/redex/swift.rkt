#lang racket/base

(require redex/reduction-semantics
         "core.rkt"
         "exn.rkt"
         "platform.rkt")

(provide Swift -->swift -->>swift)

(define-extended-ev-system Swift
  #:def-reduction -->sys
  #:def-exn-reduction -->sys/exn
  #:with-base-lang Exn
  #:with-base-reduction -->exn

  (e ::= ....
     (async/lambda (x_!_ ...) e)
     (await e)
     (timeout e e)
     (cancelled?))

  (v ::= ....
     (async/lambda (x_!_ ...) e))

  (E ::= .... (await E) (timeout E e) (timeout v E))
  (M ::= .... (await M) (timeout M e) (timeout v M))
  (G ::= .... (await G) (timeout G e) (timeout v G)))

;; NO #:binding-forms: async/lambda elimination gensym-renames its
;; parameters against the whole (store, body) itself -- see the rationale in
;; lc.rkt.

;; -----------------------------------------------------------------------------
;; Operational Semantics
;; -----------------------------------------------------------------------------

(define -->swift/core
  (reduction-relation
   Swift
   #:domain (t σ Q T P)

   [--> (t_0 σ_0 Q_0 T (FS_0 ... (thread (label (in-hole E ((async/lambda (x ..._1) e_body) v ..._1))) F ...) FS_1 ...))
        (t_1 σ_2 Q_1 T (FS_0 ... (thread (label (in-hole E x_task)) F ...) FS_1 ...))

        (where/error (σ_1 x_task v_task) (task:allocate-dependency σ_0 label))
        (where/error (x_fresh ...) (gensyms (σ_1 e_body) (x ...)))
        (where/error σ_2 (ext σ_1 (x_task v_task) (x_fresh v) ...))
        (where/error e_subst (substitute* e_body (x x_fresh) ...))
        (where/error Q_1 (Q:push Q_0 (x_task (lambda (null)
                                               (begin null
                                                      (reset
                                                       (begin
                                                         (catch (lambda (v_err)
                                                                  (task:set-failed! x_task v_err))
                                                                (task:set-done! x_task e_subst))
                                                         ;; DESTRUCTION: cancelled -- children still pending at
                                                         ;; scope exit are flagged (async-let semantics)
                                                         (task:cancel-dependencies x_task)
                                                         ;; EXTENT: task-scoped -- completion waits on children
                                                         (task:wait-on-dependencies x_task)
                                                         (os/start-soon (task:get-dependents x_task)))))))))
        (where/error t_1 t_0)
        "async-app"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (await v_awaitable))) F ...) FS_1 ...))
        (t_1 σ Q T (FS_0 ... (thread (label (in-hole E
                                                     (if (task:is-completed? v_awaitable)
                                                         (task:get-result v_awaitable)
                                                         (shift k
                                                                (task:add-self-as-dependent!
                                                                 v_awaitable
                                                                 (label (task:continue-with v_awaitable k))))))) F ...) FS_1 ...))

        (where/error t_1 t_0)
        "await"]

   ;; timeout = await-with-deadline: the deadline timer flags the child
   ;; (spawned in the E-hole). Settlement decides: a flagged child's sleeps
   ;; abort and fail it with "cancelled" (re-raised by the await); a child
   ;; that completes despite the flag returns its value. The only
   ;; cancellation source -- tasks have no cancel handle.
   [--> (t_0 σ Q T_0 (FS_0 ... (thread (label (in-hole E (timeout v_d v_task))) F ...) FS_1 ...))
        (t_1 σ Q T_1 (FS_0 ... (thread (label (in-hole E (await v_task))) F ...) FS_1 ...))

        (where #true (task:is-task? v_task))
        (where/error (struct [self (ptr x_self)] _ ...) v_task)
        (where/error t_deadline ,(+ (term t_0) (term v_d)))
        (where/error T_1 (T:push T_0 (t_deadline x_self (lambda (none)
                                                          (begin none
                                                                 (task:set-cancelled! v_task))))))
        (where/error t_1 t_0)
        "timeout"]

   [--> (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (cancelled?))) F ...) FS_1 ...))
        (t_0 σ Q T (FS_0 ... (thread (label (in-hole E (task:cancelled? σ label))) F ...) FS_1 ...))

        "cancelled?"]))


(define -->sys/overrides
  (extend-reduction-relation
   -->sys/exn
   Swift

   ;; The sleep implementation honors the cancellation convention: after
   ;; waking (due timer, or resumed early by sys/signal-cancel) it checks
   ;; (cancelled?) -- evaluated in the io frame, so the ancestor walk covers
   ;; the whole task subtree -- and raises "cancelled" instead of returning.
   [-->
    (t_0 σ_0 Q T (FS_0 ... (thread (label (in-hole E (os/io t v))) F ...) FS_1 ...))
    (t_1 σ_2 Q T (FS_0 ... (thread
                            (x_io (os/start-later (+ (os/time) t)
                                                  x_io
                                                  (lambda (none)
                                                    (begin (catch (lambda (e) (task:set-failed! x_io e))
                                                                  (begin none
                                                                         (if (cancelled?)
                                                                             (throw "cancelled")
                                                                             (task:set-done! x_io v))))
                                                           (os/start-soon (task:get-dependents x_io))))))
                            (label (in-hole E x_io)) F ...)
                  FS_1 ...))

    (where/error (σ_1 x_io v_task) (task:allocate-dependency σ_0 label))
    (where/error σ_2 (ext1 σ_1 (x_io v_task)))
    (where/error t_1 t_0)
    "os/io"]

   ;; COOPERATIVE cancellation: a timeout deadline only sets a flag
   ;; (task:cancelled? walks parents, so children observe an ancestor's
   ;; flag). Nothing is injected at dispatch -- a flagged body still runs --
   ;; so the base cancelled-dispatch rule stays disabled; only os/io's
   ;; post-wake check delivers (below).
   [-->
    (t_0 σ Q_0 T ((thread F F_rs ...) ... (thread) FS_1 ...))
    (t_1 σ Q_1 T ((thread F F_rs ...) ...
                  (thread (label_waiting (v_thunk (void))))
                  FS_1 ...))
    (where ((label_waiting v_thunk) Q_1) (Q:pop Q_0))
    (where/error t_1 t_0)
    "sys/schedule"]

   ;; Fused any-pending-timer delivery as the base sys/signal (platform.rkt),
   ;; restricted to uncancelled owners; sys/signal-cancel handles the rest.
   [-->
    (t_0 σ Q_0 ((t_a label_a v_a) ... (t_d label v) (t_b label_b v_b) ...) P)
    (t_1 σ Q_1 ((t_a label_a v_a) ... (t_b label_b v_b) ...) P)
    (where #false (task:cancelled? σ label))
    (where/error Q_1 (Q:push Q_0 (label v)))
    (where/error t_1 ,(max (term t_0) (term t_d)))
    "sys/signal"]

   [-->
    (t_0 σ Q T P)
    (t_0 σ Q T P)
    (side-condition #false)
    "sys/schedule-cancelled"]

   ;; A cancelled owner's timer resumes NOW (deadline ignored) -- an ordinary
   ;; wake-up: the raise happens in the sleep implementation's own post-wake
   ;; (cancelled?) check (see os/io above), not here.
   [-->
    (t_0 σ Q_0 ((t_a label_a v_a) ... (t_c label v) (t_b label_b v_b) ...) P)
    (t_1 σ Q_1 ((t_a label_a v_a) ... (t_b label_b v_b) ...) P)
    (where #true (task:cancelled? σ label))
    (where/error Q_1 (Q:push Q_0 (label v)))
    (where/error t_1 t_0)
    "sys/signal-cancel"]))


(define -->swift
  (union-reduction-relations
   (make-big-step -->sys/overrides)
   -->swift/core))

;; Non-collapsing variant that exposes every successor (drops the make-big-step
;; wrapper). Drives whole-state-space exploration: the directed witness search
;; (../fuzz/witness.rkt) and the reference enumerator (../fuzz/reference.rkt).
(define -->>swift
  (union-reduction-relations
   -->sys/overrides
   -->swift/core))

;; -----------------------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------------------

(module+ test
  (require (submod "core.rkt" niceties)
           "utils.rkt"
           (prefix-in unit: rackunit)
           "differential.rkt")

  ;; Swift prints booleans as true/false; the model's are #t/#f. Normalize
  ;; expected values to Swift's spelling for the runtime comparison.
  (define (swift-normalize v)
    (case v [(#t) "true"] [(#f) "false"] [else (format "~a" v)]))

  (define-syntax-rule (swift-->>= e v)
    (begin
      (test-->> -->swift #:equiv prog/equiv (async/main #:threads 2 e) v)
      (differential-output 'swift 'e v #:normalize swift-normalize)))

  (define-syntax-rule (swift-->>∈ e results)
    (begin
      (unit:check-true
       (with-exn-handler
           (evaluates-in-set -->swift (async/main #:threads 2 e) results
                             #:iterations 1
                             #:extract-result program-output)))
      (differential-in-set 'swift 'e results #:normalize swift-normalize))))

(module+ test
  (swift-->>=
   (os/block ((async/lambda () 42)))
   42)

  (swift-->>=
   (os/block ((async/lambda (x) x) 42))
   42)

  (swift-->>=
   (let* ([yield (async/lambda () (void))]
          [id (async/lambda (x)
                (begin
                  (await (yield))
                  x))])

     (os/block (id 42)))
   42)

  (swift-->>=
   (let* ([mk-t1 (async/lambda () (throw 42))]
          [mk-t2 (async/lambda (x)
                   (catch (lambda (v) v)
                          (begin
                            (await (mk-t1))
                            x)))])

     (os/block (mk-t2 0)))
   42)

  (swift-->>=
   (let ([work (async/lambda () (await (os/io 5 42)))])
     (os/block (work)))
   42)

  (swift-->>=
   (trace-stdout (print)
     (let* ([work (async/lambda (msg)
                    (begin
                      (print (await (os/io 1 msg)))
                      (print (await (os/io 1 msg)))))])
       (os/block (work "A"))))
   "AA")

  (swift-->>=
   (let* ([work (async/lambda () (cancelled?))])
     (os/block (work)))
   #false)

  ;; TIMEOUT: the deadline flags the worker; its next sleep aborts and the
  ;; settlement raises into the catch ("C" after 0-3 As). A worker that
  ;; finishes before the flag is observed returns normally ("AAA", no C).
  (swift-->>∈
   (trace-stdout (print)
     (let* ([worker (async/lambda ()
                      (letrec ([loop (lambda (i)
                                       (when (< i 3)
                                         (begin
                                           (await (os/io 1 (print "A")))
                                           (loop (+ 1 i)))))])
                        (loop 0)))]
            [main (async/lambda ()
                    (catch (lambda (e) (print "C"))
                           (begin (timeout 1 (worker)) (void))))])
       (os/block (main))))
   '("C" "AC" "AAC" "AAAC" "AAA"))

  (swift-->>∈
   (trace-stdout (print)
     (let* ([get-truth (async/lambda () #true)]
            [work (async/lambda (msg)
                    (letrec ([loop (lambda (i)
                                     (when (< i 3)
                                       (begin
                                         (when (await (get-truth))
                                           (print msg))
                                         (loop (+ 1 i)))))])
                      (loop 0)))]
            [main (async/lambda ()
                    (let ([task0 (work "A")]
                          [task1 (work "B")])
                      (begin (print "C")
                             (await task0)
                             (await task1))))])
       (os/block (main))))
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
       (os/block (main))))
   (string-permutations "ABC"))

  ;; DESTRUCT: an unawaited child is flagged at its spawner's scope exit; its
  ;; pending sleep aborts, so "B" is suppressed unless the (free-running)
  ;; timer beat the parent to completion.
  (swift-->>∈
   (trace-stdout (print)
     (let* ([child (async/lambda () (begin (await (os/io 50 (void))) (print "B")))]
            [main (async/lambda ()
                    (let ([c (child)])
                      (print "A")))])
       (os/block (main))))
   '("A" "AB" "BA"))

  ;; PROPAGATION: the timeout flags its child's whole subtree — the
  ;; grandchild's sleep aborts and the failure chains up through both awaits.
  (swift-->>∈
   (let* ([inner (async/lambda () (await (os/io 50 "I")))]
          [outer (async/lambda () (await (inner)))]
          [main (async/lambda ()
                  (catch (lambda (e) "cancelled")
                         (timeout 1 (outer))))])
     (os/block (main)))
   '("cancelled" "I"))

  ;; EXTENT + cooperative bodies: the spawner completes only after its child
  ;; settles, and a born-cancelled body still runs (prints "B") — so "D"
  ;; always trails both "A" and "B".
  (swift-->>∈
   (trace-stdout (print)
     (let* ([child (async/lambda () (print "B"))]
            [parent (async/lambda ()
                      (let ([c (child)])
                        (print "A")))]
            [main (async/lambda ()
                    (begin (await (parent)) (print "D")))])
       (os/block (main))))
   '("ABD" "BAD")))
