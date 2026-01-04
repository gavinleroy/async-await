#lang racket

(require (for-syntax racket/base)
         (for-syntax syntax/parse)
         redex/reduction-semantics
         (only-in "lc.rkt" LC lookup))

(provide (all-defined-out))

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
    (unless (and result (member result results equal?))
      (error 'evaluates-in-set "final program reduced outside of the set~%got: ~a~%expected: ~a~%" final results))))

(define (struct-slot-set s slot v)
  (unless (pair? s)
    (error 'struct-slot-set "expected a pair but got ~a" s))
  (cons 'struct (dict-update (cdr s) slot (lambda _ (list v)))))

(define (struct-slot-get s slot)
  (when (and (list? s) (eq? 'struct (car s)))
    (let* ([pairs (filter pair? (cdr s))]
           [res (assoc slot (cdr s))])
      (when res (cadr res)))))

(begin-for-syntax
  (define-syntax-rule (with-unhygenic srcloc (name ...) body)
    (with-syntax ([name (datum->syntax srcloc 'name srcloc)] ...)
      body)))

(define-syntax (define-event-loop stx)
  (syntax-case stx ()
    ((_ Lang Base)
     (with-unhygenic #'Lang (async/main
                             step
                             q-pop
                             q-push
                             any-busy?
                             all-busy?
                             new-task
                             task-coro
                             task-status
                             task-settle
                             task-fail
                             task-awaited
                             task-coro-eq?
                             task-cancel
                             task-uncancel
                             task-ready?
                             task-push-waiting
                             task-tree-owner
                             task-tree-cancelled?
                             task-tree-running-child
                             task-tree-children
                             find-unawaited-error
                             sync?
                             async?
                             value?
                             task?
                             program-output
                             prog/equiv)
       #'(begin
           (define-extended-language Lang Base
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
                (task-owner l)
                (kont F (... ...)))
  
             (t ::= natural)
  
             (l ::= sync x)
  
             (F ::= (frame e l))
  
             (Q ::= (F (... ...)))

             (FS ::= (stack F (... ...)))
  
             (P ::= (FS (... ...))))

           (define-syntax (async/main stx)
             (syntax-parse stx
               [(_ (~optional (~seq #:threads thrds:integer)) e)
                (define workers (for/list ([i (in-range 1 (syntax-e #'(~? thrds 1)))]) '(stack)))
                #`(term-let ([(thrd (... (... ...))) '#,workers])
                            (term (0 () () ((stack (frame (substitute e) sync)) thrd (... (... ...))))
                                  #:lang Lang))]))

           (define-metafunction Lang
             step : t -> t
             [(step t_0) ,(+ 1 (term t_0))])

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
             any-busy? : FS (... ...) -> boolean
             [(any-busy? _ (... ...) (stack _ _ (... ...)) _ (... ...))
              #true]
             [(any-busy? _ (... ...)) #false])

           (define-metafunction Lang
             all-busy? : FS (... ...) -> boolean
             [(all-busy? FS (... ...))
              ,(not (term (any-busy? FS (... ...))))])

           ;; =====
           ;; TASKS

           (define-metafunction Lang
             new-task : v (... ...) -> any
             [(new-task) (struct
                           [status "running"]
                           [awaited #false]
                           [cancelled #false]
                           [value (kont)])]
             [(new-task (name coro (tag _)))
              (struct
                [status "running"]
                [awaited #false]
                [cancelled #false]
                [value (kont)]
                [inner coro])]
             [(new-task (name p (task-owner _)))
              (struct
                [status "running"]
                [awaited #false]
                [cancelled #false]
                [value (kont)]
                [owner p])])

           (define-metafunction Lang
             task-coro : v -> (some v) or none
             [(task-coro v)
              (some v_coro)
              (where v_coro ,(struct-slot-get (term v) 'inner))]
             [(task-coro _)
              none])

           (define-metafunction Lang
             task-tree-owner : v -> (some l) or none
             [(task-tree-owner v)
              (some l)
              (where (task-owner l) ,(struct-slot-get (term v) 'owner))]
             [(task-tree-owner _)
              none])

           (define-metafunction Lang
             task-tree-cancelled? : σ x -> boolean
             [(task-tree-cancelled? σ x)
              #true ;; cancelled, return true
              (where/error v_obj (lookup σ x))
              (side-condition (struct-slot-get (term v_obj) 'cancelled))]
             [(task-tree-cancelled? σ x)
              (task-tree-cancelled? σ x_owner) ;; recurse to owner
              (where/error v_obj (lookup σ x))
              (where (task-owner x_owner) ,(struct-slot-get (term v_obj) 'owner))]
             [(task-tree-cancelled? σ x)
              #false])

           (define-metafunction Lang
             task-tree-running-child : σ x -> (some x) or none
             [(task-tree-running-child σ x)
              (some x_running)
              (where (x_child (... ...)) (task-tree-children σ x))
              (where x_running ,(findf (lambda (child)
                                         (term-let ([x_child child])
                                                   (term (task-ready? σ x_child))))
                                       (term (x_child (... ...)))))]
             [(task-tree-running-child _ _) none])

           (define-metafunction Lang
             task-tree-children : σ x -> (x (... ...))
             [(task-tree-children σ x)
              ,(for/list ([p (term σ)]
                          #:when (eq? (term x) (struct-slot-get (cadr p) 'owner)))
                 (car p))])
           
           (define-metafunction Lang
             task-status : v -> (done v) or (failed v) or (pending F (... ...)) or cancelled
             [(task-status (struct _ (... ...) [status "done"] _ (... ...) [value v] _ (... ...)))
              (done v)]
             [(task-status (struct _ (... ...) [status "failed"] _ (... ...) [value v] _ (... ...)))
              (failed v)]
             [(task-status (struct _ (... ...) [cancelled #true] _ (... ...)))
              cancelled]
             [(task-status (struct _ (... ...) [status "running"] _ (... ...) [value v_kont] _ (... ...)))
              (pending F (... ...))
              (where/error (kont F (... ...)) v_kont)])

           (define-metafunction Lang
             task-settle : v v -> any
             [(task-settle v_struct v)
              ,(struct-slot-set
                (struct-slot-set (term v_struct) 'status "done")
                'value
                (term v))
              (where/error "running" ,(struct-slot-get (term v_struct) 'status))])

           (define-metafunction Lang
             task-fail : v v -> any
             [(task-fail v_struct v)
              ,(struct-slot-set
                (struct-slot-set (term v_struct) 'status "failed")
                'value
                (term v))
              (where/error "running" ,(struct-slot-get (term v_struct) 'status))])

           (define-metafunction Lang
             task-awaited : v -> v
             [(task-awaited v_struct)
              ,(struct-slot-set (term v_struct) 'awaited #true)])

           (define-metafunction Lang
             task-coro-eq? : v v -> boolean
             [(task-coro-eq? v_struct v_coro)
              #true
              (where (some v_real) (task-coro v_struct))
              (side-condition (equal? (term v_real) (term v_coro)))]
             [(task-coro-eq? v_0 v_1)
              #false])

           (define-metafunction Lang
             task-cancel : v -> v
             [(task-cancel v_struct)
              ,(struct-slot-set (term v_struct) 'cancelled #true)])

           (define-metafunction Lang
             task-uncancel : any -> any
             [(task-uncancel v_struct)
              ,(struct-slot-set (term v_struct) 'cancelled #false)])

           (define-metafunction Lang
             task-ready? : σ x -> boolean
             [(task-ready? σ x)
              ,(match (term (task-status v))
                 [`(done ,_) #true]
                 [`(failed ,_) #true]
                 [else #false])
              (where/error v (lookup σ x))])

           (define-metafunction Lang
             task-push-waiting : v F -> v
             [(task-push-waiting (struct
                                   [variable_0 any_0] (... ...)
                                   [status "running"]
                                   [variable_1 any_1] (... ...)
                                   [value (kont F_frames (... ...))]
                                   [variable_2 any_2] (... ...)) F)
              (struct
                [variable_0 any_0] (... ...)
                [status "running"]
                [variable_1 any_1] (... ...)
                [value (kont F_frames (... ...) F)]
                [variable_2 any_2] (... ...))]
             [(task-push-waiting any _)
              ,(error 'task-push-waiting "task object not pending ~a" (term any))])

           ;; ================
           ;; STORE PREDICATES

           (define-metafunction Lang
             find-unawaited-error : σ -> (some v) or none
             [(find-unawaited-error (_ (... ...)
                                       (_ (struct _ (... ...)
                                            [status "failed"] _ (... ...)
                                            [awaited #false] _ (... ...)
                                            [value v] _ (... ...))) _ (... ...)))
              (some v)]
             [(find-unawaited-error _) none])

           ;; =======
           ;; HELPERS

           (define (sync? t)
             (eq? t 'sync))

           (define (async? t)
             (not (sync? t)))

           (define-metafunction Lang
             value? : any -> boolean
             [(value? v) #true]
             [(value? any) #false])

           (define-metafunction Lang
             task? : v -> boolean
             [(task? (task _)) #true]
             [(task? _) #false])

           ;; =======
           ;; TESTING

           (define (program-output p)
             (match p
               [`(,_t ,_H ,_Q ((stack (frame ,v sync)) ,_ (... ...))) v]
               [_ p]))
  
           (define (prog/equiv p v)
             ((default-equiv)
              (program-output p)
              v)))))))