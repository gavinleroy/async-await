#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics
                    oopsla26-async-await/aio)]

@title{Python asyncio}
@defmodule[oopsla26-async-await/aio]
@deftogether[(@defidform[#:kind "language" AsyncIO]
              @defthing[-->aio reduction-relation?]
              @defthing[-->>aio reduction-relation?])]{
 Lazy coroutines; @tt{spawn} (@tt{create_task}) gives indefinite
 extent; per-task @tt{cancel} delivered at suspension points.}
