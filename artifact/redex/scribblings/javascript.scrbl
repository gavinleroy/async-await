#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics
                    oopsla26-async-await/javascript)]

@title{JavaScript}
@defmodule[oopsla26-async-await/javascript]
@deftogether[(@defidform[#:kind "language" Js]
              @defthing[-->js reduction-relation?]
              @defthing[-->>js reduction-relation?])]{
 Eager promises with static suspension (an @racket[await] always
 yields). No spawn, no cancel, no timeout --- there is nothing to
 spell.}
