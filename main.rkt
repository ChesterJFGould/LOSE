#lang racket

(require
  (for-syntax
    racket/trace
    (except-in racket raise-type-error)
    racket/syntax
    (except-in syntax/parse expr/c)
    syntax/transformer
    syntax/stx
    racket/syntax-srcloc
    "lose-hol.rkt"
    "monads.rkt"))

(provide
  #%app
  #%expression
  (rename-out
    [module-begin #%module-begin]
    [my-define define]
    [sexpr-type sexpr]
    [prop-type prop]
    [fun-type =>]
    [empty-expr empty]
    [top-expr ⊤]
    [var #%top]
    [lam-expr lam]))

(define eeyore (void))

(begin-for-syntax
  (define eeyore #'eeyore)
  (define (burden-eeyore e) (syntax-property eeyore 'expansion e))
  (define (unburden-eeyore e) (syntax-property e 'expansion))

  (define-syntax-class expanded-term
    #:attributes (body)
    (pattern (~literal eeyore) #:attr body this-syntax)
    (pattern ((~literal #%expression) e:expanded-term) #:attr body #'e.body)
    (pattern ((~literal #%plain-app) f:expanded-term arg:expanded-term)
      #:attr body
      (burden-eeyore (app/stx (syntax-srcloc this-syntax) (unburden-eeyore #'f.body) (unburden-eeyore #'arg.body))))
    (pattern (~var x identifier) #:attr body (burden-eeyore (var/stx (syntax-srcloc #'x) #'x))))

  (define (elab-to-syntax e)
    (syntax-parse (local-expand e 'expression '())
      [e:expanded-term (unburden-eeyore #'e.body)]))

  (define (elab-to-syntax-ctx e ctx)
    (syntax-parse (local-expand e 'expression '() ctx)
      [e:expanded-term (unburden-eeyore #'e.body)]))
)

(define-syntax (module-begin syn)
  (syntax-parse syn
    [(_ es ...)
      (let*
        ([defs (map elab-to-syntax (syntax->list #'(es ...)))]
         [racket-defs
           (run/err (wf-module defs)
             (λ (err) (raise-wf-module-error err))
             (λ (m) (list #`(provide x) #`(define x 10))))])
        #`(#%module-begin #,@racket-defs))]))

(define-syntax (my-define stx)
  (syntax-parse stx
    [(_ x:id type expr)
     (burden-eeyore (def/stx (syntax-srcloc stx) #'x (elab-to-syntax #'type) (elab-to-syntax #'expr)))]))

(define-syntax sexpr-type
  (make-variable-like-transformer (λ (stx) (burden-eeyore (sexpr/stx (syntax-srcloc stx))))))

(define-syntax (prop-type stx)
  (syntax-parse stx
    [_ (burden-eeyore (prop/stx (syntax-srcloc stx)))]))

(define-syntax (fun-type stx)
  (syntax-parse stx
    [(_ d-stx c-stx) (burden-eeyore (fun/stx (syntax-srcloc stx) (elab-to-syntax #'d-stx) (elab-to-syntax #'c-stx)))]))

(define-syntax empty-expr
  (make-variable-like-transformer (λ (stx) (burden-eeyore (con/stx (syntax-srcloc stx) `empty)))))

(define-syntax (top-expr stx)
  (syntax-parse stx
    [_ (burden-eeyore (con/stx (syntax-srcloc stx) `⊤))]))

(define-syntax (lam-expr stx)
  (syntax-parse stx
    [(_ x:id b-stx)
     (define ctx (syntax-local-make-definition-context))
     (match-define (list new-x) (syntax-local-bind-syntaxes (list #'x) #f ctx))
     (burden-eeyore (lam/stx (syntax-srcloc stx) new-x (elab-to-syntax-ctx #'b-stx ctx)))]))

(define-syntax (var stx)
  (syntax-parse stx
    [(_ . x:id) (burden-eeyore (var/stx (syntax-srcloc stx) #'x))]))
