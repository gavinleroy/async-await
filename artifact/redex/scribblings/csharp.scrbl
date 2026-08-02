#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics
                    oopsla26-async-await/csharp)]

@title{C#}
@defmodule[oopsla26-async-await/csharp]
@deftogether[(@defidform[#:kind "language" C#]
              @defthing[-->c# reduction-relation?]
              @defthing[-->>c# reduction-relation?])]{
 Eager hot tasks with dynamic suspension (awaiting a completed task
 does not yield). No cancellation.}
