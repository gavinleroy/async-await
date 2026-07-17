#lang racket/base

;; -----------------------------------------------------------------------------
;; Place worker for the witness search's walk phase.
;;
;; One worker = one OS-level Racket place that loads every model and then loops
;; on its channel: for each job (vector lang start-state targets walk-ms) it
;; runs a fresh `walk-battery` (fuzz/witness.rkt) and replies with the list of
;; targets it witnessed. A pool of these gives the walk phase N independent
;; RNG streams in parallel; workers only ever report found witnesses, so a
;; worker's results can be merged into any search without soundness
;; bookkeeping. Send 'quit to shut a worker down.
;;
;; The first message a worker receives is its pool index, used to decorrelate
;; its RNG stream from its siblings'.
;; -----------------------------------------------------------------------------

(require racket/place
         racket/match
         "witness.rkt"
         (only-in "../aio.rkt"        -->>aio)
         (only-in "../tokio.rkt"      -->>tokio)
         (only-in "../trio.rkt"       -->>trio)
         (only-in "../smol.rkt"       -->>smol)
         (only-in "../javascript.rkt" -->>js)
         (only-in "../swift.rkt"      -->>swift)
         (only-in "../csharp.rkt"     -->>c#))

(provide witness-place-main)

(define reducers
  (hasheq 'asyncio    -->>aio
          'tokio      -->>tokio
          'trio       -->>trio
          'smol       -->>smol
          'javascript -->>js
          'swift      -->>swift
          'csharp     -->>c#))

(define (witness-place-main ch)
  (define idx (place-channel-get ch))
  (random-seed (modulo (+ (* 7919 (add1 idx)) (current-milliseconds))
                       (sub1 (expt 2 31))))
  (let loop ()
    (match (place-channel-get ch)
      [(vector lang start targets walk-ms)
       (place-channel-put ch (walk-battery (hash-ref reducers lang)
                                           start targets walk-ms))
       (loop)]
      ['quit (void)])))
