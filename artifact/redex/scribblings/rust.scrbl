#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics
                    oopsla26-async-await/rust)]

@title{Rust substrate}
@defmodule[oopsla26-async-await/rust]
@deftogether[(@defidform[#:kind "language" Rust]
              @defthing[-->rs/core reduction-relation?]
              @defthing[-->rs reduction-relation?])]{
 The bare Rust future substrate (poll-driven, no executor), shared by
 the tokio and smol towers.}
