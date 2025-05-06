#lang lose

(define my-cons (=> sexpr (=> sexpr sexpr)) (λ x (λ y (cons x y))))

(define x sexpr (cons empty empty))

(define x-symbol? prop (symbol? x))

(define s sexpr 'lambda)

(define all-sexpr-symbol prop (∀ [s : sexpr] (symbol? s)))

(define sexpr-contractible prop
  (∃ [x : sexpr] (∀ [y : sexpr] ((= sexpr) x y))))

(define true-duh prop
  (∀ [x : sexpr] (∃ [y : sexpr] ((= sexpr) x y))))
