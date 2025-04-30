#lang racket

(struct a (v))
(define a/c (struct/c a number?))

(struct b a (v))
(define b/c (struct/c b symbol?))

(match (b 10 20)
  [(b _ v) v]
  [(a v) v])

(b/c (b 10 'x))
