#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics
                    oopsla26-async-await/trio)]

@title{Python Trio}
@defmodule[oopsla26-async-await/trio]
@deftogether[(@defidform[#:kind "language" Trio]
              @defthing[-->trio reduction-relation?]
              @defthing[-->>trio reduction-relation?])]{
 Structured: tasks are nursery-scoped, a scope's end awaits its
 children, and @tt{timeout} (a cancel scope) is the only cancellation.}
