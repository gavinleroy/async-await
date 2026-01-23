#lang racket

(require redex/pict
         pict
         "lc.rkt"
         "lc+exn.rkt"
         "lc+coro.rkt"

         "swift.rkt"
         "csharp.rkt"
         "javascript.rkt"
         ;"rust.rkt"
         "python.rkt"

         "asyncio.rkt"
         ;"tokio.rkt"
         )

(struct lang (tag grammar reduction extra-nts reduction-style))

(define (mklang tag g r #:extra-nts [ents '(e v)] #:red-style [sty 'horizontal-left-align])
  (lang tag g r ents sty))

(define (render-components #:subdir [subdir "assets"] #:ext [ext "pdf"])
  (for ([l (list
            (mklang "lc" LC -->lc #:extra-nts '(e v σ))
            (mklang "exn" LC+Exn -->exn)
            (mklang "coro" LC+Coro -->coro)
            ;(mklang "rust" Rust -->rs)
            (mklang "python" Python -->py)
            
            (mklang "js" JS/Core -->js #:red-style 'vertical)
            (mklang "cs" C#/Core -->c# #:red-style 'vertical)
            (mklang "swift" Swift -->swift #:red-style 'vertical)
            ;(mklang "tokio" Tokio/Core -->tokio #:red-style 'vertical)
            (mklang "asyncio" AsyncIO/Core -->aio #:red-style 'vertical)
            (mklang "platform" C# -->c# #:extra-nts '(e t l Q F FS P))
            )])
    (parameterize ([non-terminal-gap-space 4]
                   #;[metafunction-pict-style 'left-right/compact-side-conditions])
      (render-language (lang-grammar l) (format "~a/langs/~a.~a" subdir (lang-tag l) ext)
                       #:nts (lang-extra-nts l))
      (render-reduction-relation (lang-reduction l) (format "~a/reductions/~a.~a" subdir (lang-tag l) ext)
                                 #:style (lang-reduction-style l)))))

(render-components)

(define-syntax (draw-arrows stx)
  (syntax-case stx ()
    [(_ base (from to) ...)
     #'(for/fold ([p base])
                 ([func (in-list (list (lambda (p) (pin-arrow-line 15 p from cb-find to ct-find)) ...))])
         (func p))]))

(define lang-tree
  (let* ([mk-node (lambda (txt) (cc-superimpose (text txt) (circle 50)))]
         [lc (mk-node "lc")]
         [exn (mk-node "exn")]
         [coro (mk-node "coro")]
       
         [rust (mk-node "rust")]
         [python (mk-node "python")]
         [c# (mk-node "c#")]
         [js (mk-node "js")]
         [swift (mk-node "swift")]

         [tokio (mk-node "tokio")]
         [aio (mk-node "asyncio")]
         [tree (vl-append 50
                          (vc-append 50
                                     lc
                                     (hc-append 50 exn coro)
                                     (hc-append 50 rust python c# js swift))
                          (hc-append 50 tokio aio))])
    (draw-arrows tree
                 (lc exn)
                 (lc coro)
                 (coro rust)
                 (rust tokio)
                 (coro python)
                 (exn python)
                 (python aio)
                 (exn c#)
                 (exn swift)
                 (exn js))))

(define (render-tree)
  (send (pict->bitmap lang-tree)
        save-file
        "assets/langs/lang-tree.png"
        'png))