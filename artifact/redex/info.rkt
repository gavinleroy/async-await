#lang info

(define collection "oopsla26-async-await")
(define pkg-desc
  "Executable PLT Redex models of async/await semantics across seven language runtimes (asyncio, Trio, JavaScript, C#, Swift, tokio, smol)")
(define version "1.0")
(define pkg-authors '(gavinleroy))
(define license 'MIT)

(define deps '("base" "redex-lib"))
(define build-deps '("rackunit-lib" "scribble-lib" "racket-doc"))

(define scribblings '(("scribblings/oopsla26-async-await.scrbl" ())))
