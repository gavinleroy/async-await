#lang racket/base

;; -----------------------------------------------------------------------------
;; Place worker for the witness search.
;;
;; One worker = one OS-level Racket place that loads every model and then loops
;; on its channel. Two job kinds:
;;
;;   (vector lang start targets walk-ms)
;;     one `walk-battery` (fuzz/witness.rkt); replies with the targets
;;     witnessed. Workers only ever report found witnesses, so results merge
;;     into any search without soundness bookkeeping.
;;
;;   (vector 'search lang start targets time-ms state-cap rng-seed)
;;     one COMPLETE `multi-witness-search`; replies with (list (list target
;;     verdict) ...). This is the endpoint's unit of parallelism: a lane runs
;;     several programs' searches concurrently on its pool instead of one
;;     search at a time — the slow lanes' wall is dominated by a few hard
;;     programs, and whole-search jobs let them overlap. `rng-seed` pins the
;;     walk RNG per (seed, lang, index) for reproducibility.
;;
;; Send 'quit to shut a worker down. The first message a worker receives is
;; its pool index, used to decorrelate sibling RNG streams for walk jobs.
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
