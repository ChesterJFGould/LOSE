#lang racket

(require
  (for-syntax
    racket/trace
    racket
    racket/syntax
    (except-in syntax/parse expr/c)
    syntax/transformer
    syntax/stx
    racket/syntax-srcloc
    "lose-hol.rkt"
    "monads.rkt"))

(provide
  #%app
  (rename-out
    [module-begin #%module-begin]
    [my-define define]
    [sexpr-type sexpr]
    [prop-type prop]
    [fun-type =>]
    [empty-expr empty]
    [top-expr ⊤]
    #;[var #%top]
    [lam-expr lam]))

(define eeyore (void))

(begin-for-syntax
  (define eeyore #'eeyore)
  (define (burden-eeyore e) (syntax-property eeyore 'expansion e))
  (define (unburden-eeyore e) (syntax-property e 'expansion))

  (define-syntax-class expanded-term
    #:attributes (body)
    (pattern (~literal eeyore) #:attr body (begin (println 'eeyore-case) (println this-syntax) this-syntax))
    (pattern (~var x identifier) #:attr body (begin (println #'x) (burden-eeyore (var/stx (syntax-srcloc #'x) #'x)))))

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
             (λ (err) (error "static error" err))
             (λ (m) (list #`(provide x) #`(define x 10))))])
        #`(#%module-begin #,@racket-defs))]))

(define-syntax (my-define stx)
  (syntax-parse stx
    [(_ x:id type expr)
     (burden-eeyore (def/stx (syntax-srcloc stx) #'x (elab-to-syntax #'type) (elab-to-syntax #'expr)))]))

(define-syntax (sexpr-type stx)
  (syntax-parse stx
    [_ (burden-eeyore (sexpr/stx (syntax-srcloc stx)))]))

(define-syntax (prop-type stx)
  (syntax-parse stx
    [_ (burden-eeyore (prop/stx (syntax-srcloc stx)))]))

(define-syntax (fun-type stx)
  (syntax-parse stx
    [(_ d-stx c-stx) (burden-eeyore (fun/stx (syntax-srcloc stx) (elab-to-syntax #'d-stx) (elab-to-syntax #'c-stx)))]))

(define-syntax (empty-expr stx)
  (syntax-parse stx
    [_ (burden-eeyore (con/stx (syntax-srcloc stx) `empty))]))

(define-syntax (top-expr stx)
  (syntax-parse stx
    [_ (burden-eeyore (con/stx (syntax-srcloc stx) `⊤))]))

;; TODO: Do scoping things?
(define-syntax (lam-expr stx)
  (syntax-parse stx
    [(_ x:id b-stx)
     (define ctx (syntax-local-make-definition-context))
     (syntax-local-bind-syntaxes (list #'x) #f ctx)
     (internal-definition-context-add-scopes ctx #'x)
     (define b^ (elab-to-syntax-ctx #'b-stx ctx))
     (burden-eeyore (lam/stx (syntax-srcloc stx) #'x b^))]))

(define-syntax (var stx)
  (syntax-parse stx
    [(_ . x:id) (burden-eeyore (var/stx (syntax-srcloc stx) #'x))]))
