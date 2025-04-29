#lang racket

(require
  (for-syntax racket syntax/parse "lose-hol.rkt"))

(provide
  #%app
  (rename-out
    [module-begin #%module-begin]
    [my-define define]
    [sexpr-type sexpr]
    [prop-type prop]
    [empty-expr empty]
    [top-expr ⊤]))

(define eeyore (void))

(begin-for-syntax
  (define eeyore #'eeyore)
  (define (burden-eeyore e) (syntax-property eeyore 'expansion e))
  (define (unburden-eeyore e) (syntax-property e 'expansion))

  (define-syntax-class expanded-term
    #:attributes (body)
    (pattern eeyore #:attr body this-syntax))

  (define (elab-to-syntax e)
    (syntax-parse (local-expand e 'expression '())
      [e:expanded-term (unburden-eeyore #'e.body)]))
)

(define-syntax (module-begin syn)
  (syntax-parse syn
    [(_ es ...)
      (let*
        ([defs (map elab-to-syntax (syntax->list #'(es ...)))]
         [racket-defs
           (map
             (λ (def)
               (match def
                 [`(define ,id ,type ,v)
                   (cond
                     [(and
                        (type? type)
                        (expr? v)
                        (type-check (hash) v type)
                        (realizer/expr (hash) v))
                      =>
                      (λ (v-realizer) #`(begin (provide #,id) (define #,id 'good)))]
                     [else (error 'type-checking)])]))
             defs)])
      #`(#%module-begin #,@racket-defs))]))


(define-syntax (my-define stx)
  (syntax-parse stx
    [(_ x:id type expr) (burden-eeyore `(define ,#'x ,(elab-to-syntax #'type) ,(elab-to-syntax #'expr)))]))

(define-syntax (sexpr-type stx)
  (syntax-parse stx
    [_ (burden-eeyore `sexpr)]))

(define-syntax (prop-type stx)
  (syntax-parse stx
    [_ (burden-eeyore `prop)]))

(define-syntax (empty-expr stx)
  (syntax-parse stx
    [_ (burden-eeyore `())]))

(define-syntax (top-expr stx)
  (syntax-parse stx
    [_ (burden-eeyore `⊤)]))
