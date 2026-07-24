#lang racket/base

;; -----------------------------------------------------------------------------
;; Differential gate: the directed witness search must agree with the
;; exhaustive reference-output-set wherever both run -- every output FULL
;; found must be 'producible, and an impossible target searched together with
;; the producible ones must never be. A value output covers the unpruned path.
;; Run: racket fuzz/witness-check.rkt (or via `raco test`).
;; -----------------------------------------------------------------------------

(require (only-in racket/list make-list)
         (only-in "../tokio.rkt"      -->>tokio)
         (only-in "../smol.rkt"       -->>smol)
         (only-in "../javascript.rkt" -->>js)
         (only-in "model.rkt" wrap-program)
         (only-in "reference.rkt" reference-output-set)
         "witness.rkt")

(provide check-witness)

;; A machine state whose root runs `e` directly (no stdout capture): the
;; output is `e`'s value -- the convention for value-returning programs.
(define (wrap-value e nthreads)
  `(0 () () () ((thread (root ,e)) ,@(make-list nthreads '(thread)))))

;; Probe one program. `impossible` is a target the model cannot produce; `known`
;; lists targets the model definitely CAN produce (used for value outputs, which
;; the stdout-only enumerator cannot supply as ground truth). Returns a result
;; hash; `ok?` summarizes the hard (must-pass) properties.
(define (probe name red start impossible #:known [known '()] #:lang [lang #f])
  (define-values (st outs cnt) (reference-output-set red start #:time-cap 45000))
  (define truth (sort (filter string? outs) string<?))
  ;; One multi-target search over every true output plus the impossible one --
  ;; as the fuzzer uses it. `#:lang` selects the canonical key, so this also
  ;; validates the timeless key against the reference's timeful one.
  (define targets (append truth known (list impossible)))
  (define verdicts (multi-witness-search red start targets #:lang lang))
  ;; (1) every output FULL found, plus every explicitly-known one, is producible
  (define all-producible
    (for/and ([o (in-list (append truth known))])
      (eq? (hash-ref verdicts o #f) 'producible)))
  ;; (2) the impossible target is never a false witness (ideally a proof)
  (define imp (hash-ref verdicts impossible #f))
  (define imp-ok (not (eq? imp 'producible)))
  (define ok? (and all-producible imp-ok))
  (hash 'name name 'status st 'truth truth 'all-producible all-producible
        'impossible imp 'imp-ok imp-ok 'ok? ok?))

(define (print-result r)
  (printf "~a\n" (hash-ref r 'name))
  (printf "  FULL: ~a  outputs=~s\n" (hash-ref r 'status) (hash-ref r 'truth))
  (printf "  every output producible? ~a\n" (hash-ref r 'all-producible))
  (printf "  impossible target -> ~a  (not a false witness? ~a)\n" (hash-ref r 'impossible) (hash-ref r 'imp-ok))
  (printf "  PASS? ~a\n\n" (hash-ref r 'ok?)))

;; worker prints "A", main prints "M"  (spawn? = use `spawn` vs eager application)
(define (spawn-main spawn?)
  `(let ([work (async/lambda () (print "A"))])
     (let ([main (async/lambda ()
                   (let ([w ,(if spawn? '(spawn (work)) '(work))])
                     (begin (print "M") (await w))))])
       (os/block (main)))))

;; two workers each print after an io suspension; main awaits both
(define race
  '(let ([work (async/lambda (msg) (begin (await (os/io 1 (void))) (print msg)))])
     (let ([main (async/lambda ()
                   (let ([a (spawn (work "A"))])
                     (let ([b (spawn (work "B"))])
                       (begin (await a) (await b)))))])
       (os/block (main)))))

;; value-returning program: output is 42, not a string
(define value-prog '(os/block ((async/lambda () 42))))

(define (battery)
  (list (probe "tokio spawn-main" -->>tokio (wrap-program (spawn-main #t) 2) "ZZZ" #:lang 'tokio)
        (probe "smol  spawn-main" -->>smol  (wrap-program (spawn-main #t) 2) "ZZZ" #:lang 'smol)
        (probe "js    spawn-main" -->>js    (wrap-program (spawn-main #f) 2) "ZZZ" #:lang 'javascript)
        (probe "tokio race"       -->>tokio (wrap-program race 2)            "ZZZ" #:lang 'tokio)
        (probe "tokio value=42"   -->>tokio (wrap-value value-prog 2)        99 #:known '(42) #:lang 'tokio)))

(define (check-witness #:verbose? [verbose? #t])
  (define results (battery))
  (when verbose? (for-each print-result results))
  (define all-ok (for/and ([r (in-list results)]) (hash-ref r 'ok?)))
  (when verbose?
    (printf "================ SUMMARY ================\n")
    (for ([r (in-list results)])
      (printf "  ~a: ~a\n" (hash-ref r 'name) (if (hash-ref r 'ok?) "PASS" "FAIL")))
    (printf "ALL PASS: ~a\n" all-ok))
  all-ok)

(module+ main
  (unless (check-witness)
    (error 'witness-check "witness search disagreed with FULL enumeration")))

(module+ test
  (require rackunit)
  (check-true (check-witness #:verbose? #f) "witness search must agree with FULL"))
