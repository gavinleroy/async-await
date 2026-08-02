#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics
                    oopsla26-async-await/smol)]

@title{Rust smol}
@defmodule[oopsla26-async-await/smol]
@deftogether[(@defidform[#:kind "language" Smol]
              @defthing[-->smol reduction-relation?]
              @defthing[-->>smol reduction-relation?])]{
 Lazy futures with @emph{weak} handles: dropping a task's handle
 cancels it.}
