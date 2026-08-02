#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics
                    oopsla26-async-await/typecheck)]

@title{Type checker}
@defmodule[oopsla26-async-await/typecheck]
@defproc[(type-check [e any/c] [#:rust? rust? any/c #f]) (values any/c any/c)]{
 Bidirectional type checker for surface programs; returns the fully
 annotated term and its type, or @racket[#f] on failure.}
