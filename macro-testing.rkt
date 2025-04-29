#lang racket

(require
  (for-syntax racket/syntax syntax/parse syntax/transformer))

(define-syntax (my-let stx)
  (syntax-parse stx
    [(_ [x:id v] b)
     (define new-x (generate-temporary #'x))
     (define idx (syntax-local-make-definition-context))
     (syntax-local-bind-syntaxes (list new-x) #f idx)
     (define new-new-x (internal-definition-context-add-scopes idx new-x))
     (syntax-local-bind-syntaxes
       (list #'x)
       #`(make-variable-like-transformer #'#,new-new-x)
       idx)
     (define b^ (local-expand #'b 'expression '() idx))
     #`(let ([#,new-new-x v]) #,b^)]))

(define x 20)

(my-let [x 10] x)
