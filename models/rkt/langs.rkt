#lang racket/base

(require (for-syntax racket/base racket/syntax syntax/parse)
         racket/splicing
         "pseudo.rkt")

(provide with-csharp
         with-javascript
         with-swift
         with-asyncio
         with-trio
         with-tokio
         with-smol

         splicing-with-csharp
         splicing-with-javascript
         splicing-with-swift
         splicing-with-asyncio
         splicing-with-trio
         splicing-with-tokio
         splicing-with-smol)

(begin-for-syntax
  (define dimension-defaults
    (hash '#:eagerness    '#'eager
          '#:suspension   '#'dynamic
          '#:extent       '#'indefinite
          '#:ref-strength '#'strong
          '#:destruction  '#'terminated
          '#:propagation  '#'never
          '#:awareness    '#f
          '#:direction    '#f
          '#:persistence  '#f)))

(define-syntax (define-language stx)
  (syntax-parse stx
    [(_ name:id (~alt (~once (~seq #:pool-size pool-size:expr))
                      (~once (~seq #:eagerness eagerness:expr))
                      (~once (~seq #:suspension suspension:expr))
                      (~once (~seq #:extent extent:expr))
                      (~once (~seq #:ref-strength ref-strength:expr))
                      (~once (~seq #:destruction destruction:expr))
                      (~once (~seq #:propagation propagation:expr))
                      (~optional (~seq #:awareness awareness:expr) #:defaults ([awareness #'#f]))
                      (~optional (~seq #:direction direction:expr) #:defaults ([direction #'#f]))
                      (~optional (~seq #:persistence persistence:expr) #:defaults ([persistence #'#f])))
        ...)
     (with-syntax ([with-name (format-id #'name "with-~a" #'name)]
                   [splicing-with-name (format-id #'name "splicing-with-~a" #'name)])
       #'(begin
           (define-syntax-rule (with-name body (... ...))
             (parameterize ([*pool-size* pool-size]
                            [*eagerness* eagerness]
                            [*suspension* suspension]
                            [*extent* extent]
                            [*ref-strength* ref-strength]
                            [*destruction* destruction]
                            [*propagation* propagation]
                            [*awareness* awareness]
                            [*direction* direction]
                            [*persistence* persistence])
               body (... ...)))
           (define-syntax-rule (splicing-with-name body (... ...))
             (splicing-parameterize ([*pool-size* pool-size]
                                     [*eagerness* eagerness]
                                     [*suspension* suspension]
                                     [*extent* extent]
                                     [*ref-strength* ref-strength]
                                     [*destruction* destruction]
                                     [*propagation* propagation]
                                     [*awareness* awareness]
                                     [*direction* direction]
                                     [*persistence* persistence])
               body (... ...)))))]))

(define-language csharp
  #:pool-size    8
  #:eagerness    'eager
  #:suspension   'dynamic
  #:extent       'indefinite
  #:ref-strength 'strong
  #:destruction  'terminated
  #:propagation  'never)

(define-language javascript
  #:pool-size    1
  #:eagerness    'eager
  #:suspension   'static
  #:extent       'indefinite
  #:ref-strength 'strong
  #:destruction  'awaited
  #:propagation  'never)

(define-language swift
  #:pool-size    8
  #:eagerness    'semi-eager
  #:suspension   'dynamic
  #:extent       'dynamic
  #:ref-strength 'strong
  #:destruction  'cancelled
  #:propagation  'never
  #:awareness    'aware
  #:direction    'simultaneous
  #:persistence  'persistent)

(define-language asyncio
  #:pool-size    1
  #:eagerness    'lazy
  #:suspension   'dynamic
  #:extent       'indefinite
  #:ref-strength 'weak
  #:destruction  'cancelled
  #:propagation  'never
  #:awareness    'aware
  #:direction    'bottom-up
  #:persistence  'transient)

(define-language trio
  #:pool-size    1
  #:eagerness    'lazy
  #:suspension   'dynamic
  #:extent       'dynamic
  #:ref-strength 'strong
  #:destruction  'awaited
  #:propagation  'destruction
  #:awareness    'aware
  #:direction    'bottom-up
  #:persistence  'persistent)

(define-language tokio
  #:pool-size    8
  #:eagerness    'lazy
  #:suspension   'dynamic
  #:extent       'indefinite
  #:ref-strength 'strong
  #:destruction  'cancelled
  #:propagation  'never
  #:awareness    'unaware
  #:direction    'top-down
  #:persistence  'transient)

(define-language smol
  #:pool-size    1
  #:eagerness    'lazy
  #:suspension   'dynamic
  #:extent       'indefinite
  #:ref-strength 'weak
  #:destruction  'cancelled
  #:propagation  'never
  #:awareness    'unaware
  #:direction    'top-down
  #:persistence  'transient)


(module+ test
  (require rackunit)
  (define (run-tests)
    (void)
    )

  (run-tests))
