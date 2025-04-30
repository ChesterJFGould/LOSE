#lang racket

(provide
  activate-monad-mode
  return/err
  bind/err
  do/err
  raise/err
  seq/err
  run/err
  err/c)

(define-syntax activate-monad-mode
  (syntax-rules ()
    [(_ do return bind)
     (define-syntax do
       (syntax-rules (<- = let)
         [(_ e) e]
         [(_ pat <- e es (... ...))
          (bind e (lambda (x) (match x [pat (do es (... ...))])))]
         [(_ let pat = e es (... ...))
          (match-let ([pat e]) (do es (... ...)))]
         [(_ e es (... ...))
          (bind e (lambda (x) (do es (... ...))))]))]))

;; Err E A is either (err E) or (ok A)

(struct err (val))

(struct ok (val))

;; A -> Err E A
(define (return/err a)
  (ok a))

;; (Err E A) (A -> (Err E B)) -> Err E B
(define (bind/err a f)
  (match a
    [(err e) a]
    [(ok a) (f a)]))

(activate-monad-mode do/err return/err bind/err)

;; E -> Err E A
(define (raise/err e)
  (err e))

;; (listof (Err E A)) -> (Err E (listof A))
(define (seq/err l)
  (match l
    [`() (return/err '())]
    [`(,c ,cs ...)
      (do/err
        a <- c
        as <- (seq/err cs)
        (return/err (cons a as)))]))

;; (Err E A) (E -> B) (A -> B) -> B
(define (run/err e err-case ok-case)
  (match e
    [(err e) (err-case e)]
    [(ok a) (ok-case a)]))

(define/contract (err/c e/c a/c)
  (-> contract? contract? contract?)
  (or/c (struct/c err e/c) (struct/c ok a/c)))
