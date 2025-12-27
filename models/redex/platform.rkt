#lang racket

(require redex/reduction-semantics "lc.rkt")

(provide (all-defined-out))

(define-metafunction REDEX
  q-pop : (any ...) -> (any (any ...)) or empty
  [(q-pop ()) empty]
  [(q-pop (any any_s ...))
   (any (any_s ...))])

(define-metafunction REDEX
  q-push : (any ...) any ... -> (any ...)
  [(q-push (any_s ...) any_el ...)
   (any_s ... any_el ...)])

(define-metafunction REDEX
  all-busy? : any ... -> boolean
  [(all-busy?) #true]
  [(all-busy? (stack) _ ...) #false]
  [(all-busy? (stack _ _ ...) any_s ...)
   (all-busy? any_s ...)])

(define-metafunction REDEX
  any-busy? : any ... -> boolean
  [(any-busy?) #false]
  [(any-busy? (stack _ _ ...) any_s ...)
   #true]
  [(any-busy? (stack) any_rest ...) (any-busy? any_rest ...)])

;; =====
;; TASKS

(define-metafunction REDEX
  new-task : any ... -> any
  [(new-task) (struct
                [status "running"]
                [awaited #false]
                [cancelled #false]
                [value (kont)])]
  [(new-task any_inner)
   (struct
     [status "running"]
     [awaited #false]
     [cancelled #false]
     [value (kont)]
     [inner any_inner])])

(define-metafunction REDEX
  task-coro : any -> any
  [(task-coro (struct _ ... [inner any_coro] _ ...)) any_coro]
  [(task-coro _) none])

(define-metafunction REDEX
  task-status : any -> (done any) or (failed any) or (pending any) or cancelled
  [(task-status (struct _ ... [cancelled #true] _ ...))
   cancelled]
  [(task-status (struct _ ... [status "done"] _ ... [value any_v] _ ...))
   (done any_v)]
  [(task-status (struct _ ... [status "failed"] _ ... [value any_v] _ ...))
   (failed any_v)]
  [(task-status (struct _ ... [status "running"] _ ... [value any_kont] _ ...))
   (pending any_kont)])

(define-metafunction REDEX
  task-settle : any any -> any
  [(task-settle (struct
                  [variable_0 any_0] ...
                  [status "running"]
                  [variable_1 any_1] ...
                  [value _]
                  [variable_2 any_2] ...) any)
   (struct
     [variable_0 any_0] ...
     [status "done"]
     [variable_1 any_1] ...
     [value any]
     [variable_2 any_2] ...)])

(define-metafunction REDEX
  task-fail : any any -> any
  [(task-fail (struct
                [variable_0 any_0] ...
                [status "running"]
                [variable_1 any_1] ...
                [value _]
                [variable_2 any_2] ...) any)
   (struct
     [variable_0 any_0] ...
     [status "failed"]
     [variable_1 any_1] ...
     [value any]
     [variable_2 any_2] ...)])

(define-metafunction REDEX
  task-awaited : any -> any
  [(task-awaited (struct [variable_0 any_0] ... [awaited _] [variable_s any_s] ...))
   (struct [variable_0 any_0] ... [awaited #true] [variable_s any_s] ...)])

(define-metafunction REDEX
  task-coro-eq? : any any -> boolean
  [(task-coro-eq? any_struct any_coro) #true
                                   (where any_real (task-coro any_struct))
                                   (side-condition (equal? (term any_real) (term any_coro)))]
  [(task-coro-eq? _ _) #false])

(define-metafunction REDEX
  task-cancel : any -> any
  [(task-cancel (struct [variable_0 any_0] ... [cancelled _] [variable_s any_s] ...))
   (struct [variable_0 any_0] ... [cancelled #true] [variable_s any_s] ...)])

(define-metafunction REDEX
  task-uncancel : any -> any
  [(task-uncancel (struct [variable_0 any_0] ... [cancelled _] [variable_s any_s] ...))
   (struct [variable_0 any_0] ... [cancelled #false] [variable_s any_s] ...)])

(define-metafunction REDEX
  task-ready? : any -> boolean
  [(task-ready? any)
   ,(match (term (task-status any))
     [`(done ,_) #true]
     [`(failed ,_) #true]
     [else #false])])

(define-metafunction REDEX
  task-push-waiting : any any -> any
  [(task-push-waiting (struct
                        [variable_0 any_0] ...
                        [status "running"]
                        [variable_1 any_1] ...
                        [value (kont any_frames ...)]
                        [variable_2 any_2] ...) any_frame)
   (struct
     [variable_0 any_0] ...
     [status "running"]
     [variable_1 any_1] ...
     [value (kont any_frames ... any_frame)]
     [variable_2 any_2] ...)]
  [(task-push-waiting any _)
   ,(error 'task-push-waiting "task object not pending ~a" (term any))])

;; ================
;; STORE PREDICATES

(define-metafunction REDEX
  find-unawaited-error : ((variable any) ...) -> (some any) or none
  [(find-unawaited-error ((variable_0 any_0) ...
                          (variable (struct _ ...
                                      [status "failed"] _ ...
                                      [awaited #false] _ ...
                                      [value any] _ ...)) (variable_1 any_1) ...))
   (some any)]
  [(find-unawaited-error _) none])

;; =======

(define (sync? t)
  (eq? t 'sync))

(define (async? t)
  (not (sync? t)))

(define (reduce rule term
                #:deterministic? [det? #false]
                #:max-steps [max-steps #false])
  (define iterator (if (real? max-steps)
                       (in-range max-steps)
                       (in-naturals)))
  (for/fold ([term term]
             [iterated? #false]
             #:result (and iterated? term))
            ([i iterator]
             #:do [(define next-progs (apply-reduction-relation rule term))]
             #:break (empty? next-progs))
    (match next-progs
      [(list reduced) (values reduced #true)]
      [many
       (if det?
           (error 'reduce "apply-reduction-relation returned multiple values. prog: ~a, results: ~a" term many)
           (values (car (shuffle many)) #true))])))

(define-syntax-rule (define-big-step bs ss lang)
  (define-metafunction lang
    bs : σ e -> (σ e) or stuck
    [(bs σ_0 e_0)
     (σ_1 e_1)
     (where (σ_1 e_1) 
            ,(reduce ss (term (σ_0 e_0))
                     #:deterministic? #true
                     #:max-steps 50))]
    [(⇓base _ _) stuck]))

(define (evaluates-in-set rule term results #:iterations [iters 50] #:extract-result extract #:equiv? [equiv? equal?])
  (for ([_ (in-range iters)])
    (define final (reduce rule term #:deterministic? #false))
    (define result (extract final))
    (unless (and result (member result results equiv?))
      (error 'evaluates-in-set "final program reduced outside of the set~%got: ~a~%expected: ~a~%" final results))))

(define-syntax (define-event-loop stx)
  (syntax-case stx ()
    ((_ Lang Base)
     #'(define-extended-language Lang Base
         (e ::= ....
            (block e)
            (os/time)
            (os/io e e)
            (os/resolve e e e))

         (E ::= ....
            (block E)
            (os/io E e)
            (os/io v E)
            (os/resolve E e e)
            (os/resolve v E e)
            (os/resolve v v E))

         (v ::= ....
            (kont F (... ...)))
  
         (t ::= natural)
  
         (l ::= sync x)
  
         (F ::= (frame e l))
  
         (Q ::= (F (... ...)))

         (FS ::= (stack F (... ...)))
  
         (P ::= (FS (... ...)))))))

;; TODO, I can't figure out the binding scopes ...
#;(begin
           
    (define-metafunction Lang
      q-pop : Q -> (F Q) or empty
      [(q-pop ()) empty]
      [(q-pop (F F_s (... ...)))
       (F (F_s (... ...)))])

    (define-metafunction Lang
      q-push : Q F (... ...) -> Q
      [(q-push (F_s (... ...)) F_el (... ...))
       (F_s (... ...) F_el (... ...))])

    (define-metafunction Lang
      all-busy? : FS (... ...) -> boolean
      [(all-busy?) #true]
      [(all-busy? (stack) _ (... ...)) #false]
      [(all-busy? (stack _ _ (... ...)) FS_s (... ...))
       (all-busy? FS_s (... ...))])

    (define-metafunction Lang
      any-busy? : FS (... ...) -> boolean
      [(any-busy?) #false]
      [(any-busy? (stack _ _ (... ...)) FS_s (... ...))
       #true]
      [(any-busy? (stack) FS_rest (... ...)) (any-busy? FS_rest (... ...))])

    (define-metafunction Lang
      value? : any -> boolean
      [(value? v) #true]
      [(value? any) #false]))