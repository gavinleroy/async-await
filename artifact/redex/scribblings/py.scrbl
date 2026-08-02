#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics
                    oopsla26-async-await/py)]

@title{Python substrate}
@defmodule[oopsla26-async-await/py]
@deftogether[(@defidform[#:kind "language" Py]
              @defthing[-->py/core reduction-relation?]
              @defthing[-->py reduction-relation?])]{
 The bare Python coroutine substrate (no scheduler), shared by the
 asyncio and Trio towers.}
