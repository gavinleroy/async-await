#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics
                    oopsla26-async-await/swift)]

@title{Swift}
@defmodule[oopsla26-async-await/swift]
@deftogether[(@defidform[#:kind "language" Swift]
              @defthing[-->swift reduction-relation?]
              @defthing[-->>swift reduction-relation?])]{
 Structured, semi-eager: async calls are @tt{async let} children,
 cancelled and implicitly awaited at scope exit; @racket[timeout] is
 the only cancellation source and flags a whole subtree.}
