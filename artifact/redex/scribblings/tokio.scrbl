#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics
                    oopsla26-async-await/tokio)]

@title{Rust tokio}
@defmodule[oopsla26-async-await/tokio]
@deftogether[(@defidform[#:kind "language" Tokio]
              @defthing[-->tokio reduction-relation?]
              @defthing[-->>tokio reduction-relation?])]{
 Lazy futures; a spawned task @emph{detaches} when its handle drops;
 @tt{cancel} is @tt{JoinHandle::abort}.}
