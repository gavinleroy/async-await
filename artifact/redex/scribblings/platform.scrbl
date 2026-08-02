#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics
                    (only-in oopsla26-async-await/platform
                             define-extended-ev-system))]

@title{Platform}
@defmodule[oopsla26-async-await/platform]

The machine every async language runs on. A configuration is
@tt{(t σ Q T P)}:

@racketgrammar*[
 [t natural]
 [label x root]
 [Q ((label (lambda (x) e)) ...)]
 [T ((t label (lambda (x) e)) ...)]
 [F (label e)]
 [FS (thread F ...)]
 [P (FS ...)]]

a logical clock, the store, a ready queue of labeled thunks, a timer
table of thunks due at a deadline, and a pool of threads, each a stack
of labeled frames. The platform also extends the expression grammar
with the @tt{os/*} hooks a language's rules schedule work through:

@racketgrammar*[
 [e ....
    (os/block e)
    (os/time)
    (os/io e_delay e)
    (os/start-soon e)
    (os/start-later e_time label e)]]

@tt{os/block} parks the root thread on an awaitable (this is how a
program's @tt{main} runs); @tt{os/io} performs I/O that takes @emph{at
least} @tt{e_delay} logical steps --- time is logical, and the clock
jumps to pending deadlines rather than ticking.

@defform[(define-extended-ev-system Lang
           #:def-reduction red-id
           maybe-exn-reduction
           #:with-base-lang base-lang-id
           #:with-base-reduction base-red
           maybe-single-threaded
           maybe-serial-dispatch
           grammar-clause ...
           maybe-binding-forms)
         #:grammar
         ([maybe-exn-reduction (code:line)
                               (code:line #:def-exn-reduction red/exn-id)]
          [maybe-single-threaded (code:line) #:single-threaded]
          [maybe-serial-dispatch (code:line) #:serial-dispatch]
          [maybe-binding-forms (code:line)
                               (code:line #:binding-forms spec ...)])]{

 Defines @racket[Lang] as @racket[base-lang-id] (usually @tt{Exn})
 extended first with the machine above, then with your
 @racket[grammar-clause]s --- new expression forms @emph{and} their
 evaluation-context holes (@tt{E}, @tt{M}, @tt{G}). It binds
 @racket[red-id] to the generated scheduler relation over @tt{(t σ Q T
 P)}: dispatch, timer delivery, @tt{os/io}, @tt{os/block}, and garbage
 collection; @racket[red/exn-id], when requested, layers exception
 propagation over it. Your language's own rules go in a separate
 @racket[reduction-relation] over the same domain, unioned with the
 generated one.

 @racket[#:single-threaded] makes synchronous code run unbounded on one
 thread (an infinite loop blocks the runtime, as in a real event loop);
 @racket[#:serial-dispatch] selects run-to-completion event-loop
 dispatch, microtasks before timers. They are independent --- Trio uses
 the first without the second.

 The form also injects (deliberately unhygienically) the vocabulary
 your rules will use: @tt{async/main} (wraps a surface program into an
 initial machine state, @tt{(async/main #:threads n e)});
 @tt{make-big-step} (collapses deterministic scheduler spines);
 @tt{program-output} and @tt{prog/equiv} (observation and equivalence
 for tests); queue operations @tt{Q:push}/@tt{Q:pop} and
 @tt{T:push}/@tt{T:pop}; and the @tt{task:*} family ---
 @tt{task:allocate}, @tt{task:set-done!}, @tt{task:set-failed!},
 @tt{task:set-cancelled!}, @tt{task:is-completed?},
 @tt{task:continue-with}, @tt{task:add-self-as-dependent!},
 @tt{task:get-dependents}, and friends.}

@section{Sketch: an eager async language}

Condensed from @racketmodname[oopsla26-async-await/javascript], the
smallest complete instance. First the language:

@racketblock[
(define-extended-ev-system Toy
  #:def-reduction -->sys
  #:def-exn-reduction -->sys/exn
  #:with-base-lang Exn
  #:with-base-reduction -->exn
  #:single-threaded
  #:serial-dispatch

  (e ::= .... (async/lambda (x ...) e) (await e))
  (v ::= .... (async/lambda (x ...) e))
  (E ::= .... (await E))
  (M ::= .... (await M))
  (G ::= .... (await G)))
]

Then the semantic decision --- here, @emph{eager} calls: applying an
@tt{async/lambda} allocates a task and runs the body immediately on the
calling thread, inside a @racket[reset] so an @racket[await] in the
body can suspend it; settling the task wakes its dependents:

@racketblock[
(define -->toy/core
  (reduction-relation
   Toy
   #:domain (t σ Q T P)
   [--> (t σ_0 Q T (FS_0 (... ...)
                    (thread (label (in-hole E ((async/lambda (x (... ...)) e_body)
                                               v (... ...))))
                            F (... ...))
                    FS_1 (... ...)))
        (t σ_2 Q T (FS_0 (... ...)
                    (thread (x_task (reset
                                     (begin
                                       (catch (lambda (v_err) (task:set-failed! x_task v_err))
                                              (task:set-done! x_task e_subst))
                                       (os/start-soon (task:get-dependents x_task)))))
                            (label (in-hole E x_task))
                            F (... ...))
                    FS_1 (... ...)))
        (where/error (σ_1 x_task v_task) (task:allocate σ_0))
        (where/error (x_fresh (... ...)) (gensyms (σ_1 e_body) (x (... ...))))
        (where/error σ_2 (ext σ_1 (x_task v_task) (x_fresh v) (... ...)))
        (where/error e_subst (substitute* e_body (x x_fresh) (... ...)))
        "async-app"]))
]

An @tt{await} rule follows the same shape (capture the continuation
with @racket[shift]; park it with @tt{task:add-self-as-dependent!} or
reschedule it with @tt{os/start-soon} if the task already settled), and
the whole language is the union:

@racketblock[
(define -->toy
  (union-reduction-relations (make-big-step -->sys/exn) -->toy/core))
]

Run a program by wrapping it into an initial state:
@racket[(test-->> -->toy (async/main #:threads 1 e) v)]. For the
remaining decisions a real language forces --- dispatch order,
destruction at scope exit, cancellation delivery --- read the seven
instances; each rule is named after the runtime behavior it mimics.
