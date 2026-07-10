#lang racket/base

;; -----------------------------------------------------------------------------
;; Reference output-set enumerator — the trusted oracle for differential testing.
;;
;; This is NOT used in the fuzzer's hot path. The fuzzer decides membership with
;; the directed witness search (witness.rkt); this module is the deliberately
;; simple, obviously-correct algorithm that the witness search is validated
;; AGAINST (fuzz/witness-check.rkt): a second implementation, by exhaustion, to
;; check the clever one on the small programs where both can run.
;;
;; `reference-output-set` drives the non-collapsing relation `-->>lang` (the
;; language modules' variant that exposes every successor, rather than the
;; sampler's `-->lang`, which collapses each system run to one random successor)
;; over the whole reachable state graph and collects every terminal's output.
;; Two things keep it tractable:
;;   - canonicalize (model.rkt) dedups states modulo alpha-renaming, store
;;     ordering, and timer-queue order;
;;   - run-to-decision collapses deterministic (single-successor) runs, so a
;;     thread's synchronous chunk counts as one step.
;;
;; It exhausts a *given program's* output set, and so terminates only for
;; low-concurrency programs: a few genuinely-concurrent workers produce
;; hundreds–thousands of inequivalent interleavings (see FUZZ.md). That is fine
;; for its job — the witness search only needs checking on the small cases.
;; -----------------------------------------------------------------------------

(require redex/reduction-semantics
         (only-in "model.rkt" canonicalize program-output))

(provide reference-output-set)

;; Immediate successors of `s` under `red`, deduped by canonical form.
(define (successors red s)
  (define raw
    (with-handlers ([exn:fail? (lambda (_) '())])
      (apply-reduction-relation red s)))
  (define seen (make-hash))
  (for/fold ([acc '()] #:result (reverse acc)) ([s* (in-list raw)])
    (define c (canonicalize s*))
    (cond [(hash-has-key? seen c) acc]
          [else (hash-set! seen c #t) (cons s* acc)])))

;; Follow deterministic (single-successor) steps from `s` until a branch or a
;; terminal. Returns (cons 'terminal final-state) | (cons 'branch branch-state).
(define (run-to-decision red s)
  (let loop ([s s] [fuel 100000])
    (define succs (successors red s))
    (cond
      [(null? succs) (cons 'terminal s)]
      [(or (pair? (cdr succs)) (<= fuel 0)) (cons 'branch s)]
      [else (loop (car succs) (sub1 fuel))])))

;; Enumerate the COMPLETE output set reachable from machine state `start` under
;; the non-collapsing reduction `red` (a -->>lang).
;;
;; Returns (values status outputs count):
;;   status  : 'complete | 'capped | 'timed-out
;;   outputs : list of distinct terminal stdout strings
;;   count   : number of distinct decision states explored
(define (reference-output-set red start
                              #:state-cap [state-cap 200000]
                              #:time-cap  [time-cap-ms 60000])
  (define start-ms (current-inexact-milliseconds))
  (define explored (make-hash))   ; canonical decision-state -> #t
  (define outputs  (make-hash))   ; output-string -> #t
  (define count 0)
  (define status 'complete)
  (define (over-cap?)
    (cond [(>= count state-cap) (set! status 'capped) #t]
          [(> (- (current-inexact-milliseconds) start-ms) time-cap-ms)
           (set! status 'timed-out) #t]
          [else #f]))
  ;; DFS over decision states (each a run-to-decision result); `explored` dedups
  ;; modulo canonicalize, which also bounds the search on any cyclic graph.
  (let/ec escape
    (define (dfs node terminal?)
      (define cs (canonicalize node))
      (unless (hash-has-key? explored cs)
        (hash-set! explored cs #t)
        (when (over-cap?) (escape (void)))
        (set! count (add1 count))
        (cond
          [terminal?
           (define o (program-output node))
           (when (string? o) (hash-set! outputs o #t))]
          [else
           (for ([s* (in-list (successors red node))])
             (define cn (run-to-decision red s*))
             (dfs (cdr cn) (eq? (car cn) 'terminal)))])))
    (define r0 (run-to-decision red start))
    (dfs (cdr r0) (eq? (car r0) 'terminal)))
  (values status (hash-keys outputs) count))
