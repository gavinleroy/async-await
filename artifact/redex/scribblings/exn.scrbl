#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics
                    oopsla26-async-await/exn)]

@title{Exceptions}
@defmodule[oopsla26-async-await/exn]
@deftogether[(@defidform[#:kind "language" Exn]
              @defthing[-->exn/core reduction-relation?]
              @defthing[-->exn reduction-relation?])]{
 @racketmodname[oopsla26-async-await/lc] plus exceptions.
 @racket[-->exn/core] contains just the new rules; @racket[-->exn] is
 the full language reduction.}

The grammar extension:

@racketgrammar*[
 [e ....
    (throw e)
    (catch e_handler e_try)
    (throw-in e_coro e_exn)]]

A @racket[throw] unwinds --- through a dedicated propagation context,
@tt{G} --- to the nearest enclosing @racket[catch], whose handler
receives the payload. @racket[throw-in] is the asynchronous variant: it
arms a suspended coroutine so that the exception raises @emph{inside}
it when it next resumes. The async languages implement cancellation
with it --- a cancelled task is one that wakes up to an exception it
never threw.
