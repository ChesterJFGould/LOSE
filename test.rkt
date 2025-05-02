#lang lose

(define my-cons (=> sexpr (=> sexpr sexpr)) cons)

(define x sexpr (cons empty empty))

(define x-symbol? prop (symbol? x))

(define s sexpr 'lambda)
