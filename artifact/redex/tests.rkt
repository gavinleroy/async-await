#lang racket/base

;; -----------------------------------------------------------------------------
;; Test runner
;;
;; Runs the `test` submodule of every language model from one place, without
;; needing raco:
;;
;;   racket tests.rkt
;;
;; Comment out a require below to disable that language's tests.
;; -----------------------------------------------------------------------------

(module+ main
  (require (submod "py.rkt" test)
           (submod "rust.rkt" test)
           (submod "aio.rkt" test)
           (submod "trio.rkt" test)
           (submod "javascript.rkt" test)
           (submod "csharp.rkt" test)
           (submod "swift.rkt" test)
           (submod "tokio.rkt" test)
           (submod "smol.rkt" test)))
