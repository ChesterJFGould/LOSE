#lang racket

(require
  (for-syntax
    racket/trace
    (except-in racket raise-type-error) racket/syntax
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
    [cons-expr cons]
    [empty-expr empty]
    [symbol?-expr symbol?]
    [->-expr ->]
    [and-expr and]
    [or-expr or]
    [top-expr ⊤]
    [bot-expr ⊥]
    [var #%top]
    [lam-expr λ]
    [equ-expr =]
    [all-expr forall]
    [better-forall ∀]
    [exi-expr exists]
    [hole _]
    [ann-expr the]
    [better-exists ∃]
    [sym-quote quote]))

(define eeyore (void))

(begin-for-syntax
  (define eeyore #'eeyore)
  (define (burden-eeyore e) (syntax-property eeyore 'expansion e))
  (define (unburden-eeyore e) (syntax-property e 'expansion))

  (define-syntax-class expanded-term
    #:attributes (body)
    (pattern (~literal eeyore) #:attr body this-syntax)
    (pattern ((~literal #%expression) e:expanded-term) #:attr body #'e.body)
    (pattern ((~literal #%plain-app) f:expanded-term arg:expanded-term args:expanded-term ...)
      #:attr body
      (burden-eeyore
        (foldl
          (λ (a f)
            (app/stx (syntax-srcloc this-syntax)
              f
              (unburden-eeyore a)))
          (app/stx (syntax-srcloc this-syntax) (unburden-eeyore #'f.body) (unburden-eeyore #'arg.body))
          (syntax->list #'(args.body ...)))))
    (pattern (~var x identifier) #:attr body (burden-eeyore (var/stx (syntax-srcloc #'x) #'x))))

  (define (elab-to-syntax e)
    (syntax-parse (local-expand e 'expression '())
      [e:expanded-term (unburden-eeyore #'e.body)]))

  (define (elab-to-syntax-ctx e ctx)
    (syntax-parse (local-expand e 'expression '() ctx)
      [e:expanded-term (unburden-eeyore #'e.body)]))

  (define (mk-constant c)
    (make-variable-like-transformer (λ (stx) (burden-eeyore (c (syntax-srcloc stx))))))
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
  (mk-constant (λ (loc) (sexpr/stx loc))))

(define-syntax prop-type
  (mk-constant (λ (loc) (prop/stx loc))))

(define-syntax (fun-type stx)
  (syntax-parse stx
    [(_ d-stx c-stx) (burden-eeyore (fun/stx (syntax-srcloc stx) (elab-to-syntax #'d-stx) (elab-to-syntax #'c-stx)))]))

(define-syntax cons-expr
  (mk-constant (λ (loc) (con/stx loc `cons))))

(define-syntax symbol?-expr
  (mk-constant (λ (loc) (con/stx loc `symbol?))))

(define-syntax empty-expr
  (mk-constant (λ (loc) (con/stx loc `empty))))

(define-syntax ->-expr
  (mk-constant (λ (loc) (con/stx loc `->))))

(define-syntax and-expr
  (mk-constant (λ (loc) (con/stx loc `and))))

(define-syntax or-expr
  (mk-constant (λ (loc) (con/stx loc `or))))

(define-syntax top-expr
  (mk-constant (λ (loc) (con/stx loc `⊤))))

(define-syntax bot-expr
  (mk-constant (λ (loc) (con/stx loc `⊥))))

(define-syntax hole
  (mk-constant (λ (loc) (hole/stx loc))))

(define-syntax (lam-expr stx)
  (syntax-parse stx
    [(_ x:id b-stx)
     (define ctx (syntax-local-make-definition-context))
     (match-define (list new-x) (syntax-local-bind-syntaxes (list #'x) #f ctx))
     (burden-eeyore (lam/stx (syntax-srcloc stx) new-x (elab-to-syntax-ctx #'b-stx ctx)))]))

(define-syntax (var stx)
  (syntax-parse stx
    [(_ . x:id) (burden-eeyore (var/stx (syntax-srcloc stx) #'x))]))

(define-syntax (sym-quote stx)
  (syntax-parse stx
    [(_ s:identifier) (burden-eeyore (sym/stx (syntax-srcloc stx) (syntax-e #'s)))]))

(define-syntax (equ-expr stx)
  (syntax-parse stx
    [(_ t) (burden-eeyore (equ/stx (syntax-srcloc stx) (elab-to-syntax #'t)))]))

(define-syntax (all-expr stx)
  (syntax-parse stx
    [(_ t) (burden-eeyore (all/stx (syntax-srcloc stx) (elab-to-syntax #'t)))]))

(define-syntax (exi-expr stx)
  (syntax-parse stx
    [(_ t) (burden-eeyore (exi/stx (syntax-srcloc stx) (elab-to-syntax #'t)))]))

(define-syntax (ann-expr stx)
  (syntax-parse stx
    [(_ t e) (burden-eeyore (ann/stx (syntax-srcloc stx) (elab-to-syntax #'e) (elab-to-syntax #'t)))]))

(define-syntax (app-helper stx)
  (syntax-parse stx
    [(_ f a) (burden-eeyore (app/stx (syntax-srcloc stx) (elab-to-syntax #'f) (elab-to-syntax #'a)))]))

(define-syntax better-exists
  (syntax-rules (:)
    [(_ [x : t] b)
      (app-helper (exi-expr t) (lam-expr x b))]))

(define-syntax better-forall
  (syntax-rules (:)
    [(_ [x : t] b)
      (app-helper (all-expr t) (lam-expr x b))]))
