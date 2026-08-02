#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics)]

@title{Executable Models of Async/Await}
@author{Gavin Gray}

What does @racket[await] mean? More things than you think, and the
differences are observable. This package contains executable PLT Redex
semantics for the async/await implementations of seven runtimes ---
Python's @tt{asyncio} and Trio, JavaScript, C#, Swift, and Rust's
@tt{tokio} and @tt{smol}. These are not sketches: each model has been
validated against its real runtime (the paper's artifact, distributed as
a Docker image at @tt{ghcr.io/gavinleroy/async-await}, reproduces that
validation).

@section{The Tower}

Each language model is the top floor of a small tower, and only the top
floor differs between languages:

@itemlist[

 @item{@racketmodname[oopsla26-async-await/lc] --- a call-by-value
  λ-calculus with state, lists, structs, and delimited control. The
  control operators (@tt{reset}/@tt{shift}) are how tasks suspend;
  everything else is furniture.}

 @item{@racketmodname[oopsla26-async-await/exn] --- exceptions:
  @tt{throw}, @tt{catch}, and @tt{throw-in}, which raises @emph{inside}
  a suspended coroutine. Cancellation will want that.}

 @item{@filepath{platform.rkt} --- the machine. A configuration is
  @tt{(t σ Q T P)}: a logical clock, a store, a ready queue, a timer
  table, and a pool of threads. The platform supplies blocking
  (@tt{os/block}), timed I/O (@tt{os/io}), the scheduler rules, and the
  @tt{define-extended-ev-system} form that each language instantiates.
  Time is logical: @tt{os/io} promises @emph{at least} its delay, and
  the clock jumps to pending deadlines.}

 @item{one module per language --- the surface forms
  (@tt{async/lambda}, @tt{await}, and whichever of spawn, cancel, or
  timeout the language actually offers) and their reduction rules.}

]

The payoff of the layering: when two models disagree about a program,
the disagreement lives in one file, and it is a semantic decision, not
plumbing.

@section{Module Reference}

Every language module exports exactly three identifiers, consistently
named. For a language @tt{L}: the language itself; @tt{-->L}, the
relation that runs programs (deterministic scheduler spines are
collapsed into single steps, so @racket[test-->>] converges quickly);
and @tt{-->>L}, the non-collapsing variant that exposes @emph{every}
successor state --- use it when you want the whole interleaving space,
not just an execution.

@include-section["lc.scrbl"]
@include-section["exn.scrbl"]
@include-section["platform.scrbl"]
@include-section["aio.scrbl"]
@include-section["trio.scrbl"]
@include-section["javascript.scrbl"]
@include-section["csharp.scrbl"]
@include-section["swift.scrbl"]
@include-section["tokio.scrbl"]
@include-section["smol.scrbl"]
@include-section["py.scrbl"]
@include-section["rust.scrbl"]
@include-section["typecheck.scrbl"]

@section{Writing Your Own}

Suppose your language isn't here. Resist the urge to start from
nothing.

@itemlist[#:style 'ordered

 @item{@bold{Pick the nearest neighbor and copy it.} Eager task start?
  Read @racketmodname[oopsla26-async-await/csharp] or
  @racketmodname[oopsla26-async-await/swift]. Lazy? Read
  @racketmodname[oopsla26-async-await/aio] or
  @racketmodname[oopsla26-async-await/tokio].}

 @item{@bold{Decide the semantics before writing rules.} Four questions
  do most of the work: Does calling an async function run it (eager) or
  build a value (lazy)? Does awaiting a completed task suspend anyway?
  What keeps an unawaited task alive --- a handle, the runtime, a scope?
  And who dies at cancellation --- a task, or a tree of them? Every pair
  of answers you can observe with a three-line program; the models exist
  because runtimes answer differently.}

 @item{@bold{Extend the machine.} @tt{define-extended-ev-system} takes
  your new expression forms @emph{and} their evaluation-context holes
  (@tt{E}, @tt{M}, @tt{G}). Forgetting the holes is the classic
  mistake: your form will parse and then silently never reduce.}

 @item{@bold{Write the scheduler interaction as rules.} Dispatch (what
  runs next) and delivery (what a due or cancelled timer does) are where
  languages hide their personality. Keep each rule small; name it after
  the runtime behavior it mimics.}

 @item{@bold{Test with @racket[test-->>].} Start with the three-line
  observation programs from step 2, and run them against the real
  language too --- by hand is fine. That comparison is where our
  models' bugs were found, and yours will be too.}

]

@section{Testing}

Each model's @racket[test] submodule is pure Redex --- no external
toolchains required. The full validation against the real runtimes is
part of the paper's artifact, not this package.
