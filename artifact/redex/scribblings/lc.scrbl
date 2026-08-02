#lang scribble/manual

@require[(for-label racket/base
                    redex/reduction-semantics
                    oopsla26-async-await/lc)]

@title{Core calculus}
@defmodule[oopsla26-async-await/lc]
@deftogether[(@defidform[#:kind "language" LC]
              @defthing[-->lc reduction-relation?])]{
 The sequential core: a call-by-value λ-calculus over states @tt{(σ e)}
 --- a store paired with the running expression. @racket[-->lc] is its
 standard reduction.}

The grammar, abridged (arithmetic, comparison, and string forms
elided):

@racketgrammar*[
 [e x
    v
    (e e ...)
    (if e e e)
    (let ([x e] ...) e)
    (letrec ([x e] ...) e)
    (begin e ...)
    (set! x e)
    (reset e)
    (shift x e)
    (box e) (unbox e) (set-box! e e)
    (list e ...) (cons e e) (car e) (cdr e) (empty? e)
    (struct [x e] ...) (field x e)]
 [v number
    string
    boolean
    (void)
    (ptr x)
    (lambda (x ...) e)
    (list v ...)
    (struct [x v] ...)]]

Two features earn their keep. @racket[reset]/@racket[shift] are
delimited control --- every async language above builds task suspension
out of them: a task body runs inside a @racket[reset], and awaiting
captures the rest of the body with @racket[shift] as a continuation to
park. And the store σ maps names to values through @tt{(ptr x)}
references, so tasks, boxes, and structs are heap objects that survive
across suspensions.
