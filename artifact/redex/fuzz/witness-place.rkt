#lang racket/base

;; -----------------------------------------------------------------------------
;; Place worker for the witness search: one Racket place loads every model and
;; loops on its channel. A (vector lang ...) job runs one walk-battery; a
;; (vector 'search ...) job runs one complete multi-witness-search (the unit
;; of parallelism; rng-seed pins the walk RNG). 'quit stops; the first message
;; is the pool index (decorrelates sibling RNG streams).
;; -----------------------------------------------------------------------------

(require racket/place
         racket/match
         "witness.rkt"
         (only-in "model.rkt" canon-for-lang)
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
      [(vector 'search lang start targets time-ms state-cap rng-seed)
       (random-seed rng-seed)
       (define verdicts
         (multi-witness-search (hash-ref reducers lang) start targets
                               #:time-cap time-ms
                               #:state-cap state-cap
                               #:lang lang))
       (place-channel-put ch (for/list ([(k v) (in-hash verdicts)])
                               (list k v)))
       (loop)]
      [(vector lang start targets walk-ms)
       (place-channel-put ch (walk-battery (hash-ref reducers lang)
                                           start targets walk-ms
                                           #:canon (canon-for-lang lang)))
       (loop)]
      ['quit (void)])))
