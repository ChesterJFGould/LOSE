#lang racket

(provide (all-defined-out))

;; sexpr ::=
;;   | x
;;   | `(cons ,sexpr ,sexpr)
;;   | `(quote ,symbol?)
;;   | `()
;;
;; prop ::=
;;   | x
;;   | (= sexpr sexpr)
;;   | (exists x prop)

(define (prop? p)
  (match p
    [(? symbol?) #t]
    [`(= ,a ,b) (and (sexpr? a) (sexpr? b))]
    [`(exists ,(? symbol? x) ,b) (prop? b)]
    [_ #f]))

(define (sexpr? e)
  (symbol? e))

;; proof ::=
;;   | x
;;   | (existsI sexpr proof)
;;   | (existsE (x x) proof proof)

(define (proof? p)
  (match p
    [(? symbol?) #t]
    [`(existsI ,a ,prf)
      (and (sexpr? a) (proof? prf))]
    [`(existsE (,(? symbol? x) ,(? symbol? y)) ,a ,b)
      (and (proof? a) (proof? b))]
    [_ #f]))

;; env ::= dictof x hyp
;; hyp ::=
;;   | prop
;;   | sexpr
;;   | (,prop true)

(define (env? e)
  (dict? e))

(define (hyp? h)
  (match h
    [`prop #t]
    [`sexpr #t]
    [`(,p true) (prop? p)]))

;; judgment ::=
;;   | [,prop prop]
;;   | [,sexpr sexpr]
;;   | [,prop true]

(define (judgement? j)
  (match j
    [`(,p prop)
      (prop? p)]
    [`(,a sexpr)
      (sexpr? a)]
    [`(,p true)
      (prop? p)]))

;; [,env |- ,prop prop]
;; [,env |- ,sexpr sexpr]
;; [,env |- ,proof : ,judgement]

;; (dict-ref env x) = 'sexpr
;; ------------------------- varS
;; ,env |- ,x sexpr
;;
;; (dict-ref env x) = 'prop
;; ------------------------- varP
;; ,env |- ,x prop
;;
;; ,env |- ,a sexpr    ,env |- ,b sexpr
;; ------------------------------------ =P
;; ,env |- (= ,a ,b) prop
;;
;; ,(dict-set env x `sexpr) |- ,b prop
;; ------------------------------------ existsP
;; ,env |- (exists ,x ,b) prop
;;
;; ,env |- ,a sexpr    ,env |- ,prf : ,(subst/prop p x a)
;; ------------------------------------------
;; ,env |- (existsI ,a ,prf) : ((exists ,x ,p) true)

(define/contract (sexprJ env s)
  (-> env? sexpr? boolean?)
  (match s
    [(and (? symbol?) (app (λ (x) (dict-ref env x #f)) `sexpr)) #t]
    [_ #f]))

(define/contract (propJ env p)
  (-> env? sexpr? boolean?)
  (match p
    [(and (? symbol?) (app (λ (x) (dict-ref env x #f)) `prop)) #t]
    [`(= ,a ,b)
      (and (sexprJ env a) (sexprJ env b))]
    [`(exists ,x ,b)
      (propJ (dict-set env x 'sexpr) b)]
    [_ #f]))

(define/contract (checkJ env prf j)
  (-> env? proof? judgement? boolean?)
  (match* (prf j)
    [(`(existsI ,a ,prf) `((exists ,x ,p) true))
     (and (sexprJ env a) (checkJ env prf `(,(subst/prop p x a) true)))]
    [(`(existsE (,x ,y) ,p ,q) j)
      (match (synthJ env p)
        [`((exists ,z ,r) true)
          (checkJ
            (dict-set (dict-set env x 'sexpr) y `(,(subst/prop r z x) true))
            q
            j)]
        [_ #f])]
    [(prf j)
     (cond
       [(synthJ env prf)
        =>
        (λ (k) (alpha-equiv/judgement? j k))]
       [else #f])]))

(define/contract (synthJ env prf)
  (-> env? proof? (or/c judgement? #f))
  (match prf
    [(? symbol? x)
     (match (dict-ref env x #f)
       [`(,p true)
        `(,p true)]
       [`prop
        `(,x prop)]
       [`sexpr
        `(,x sexpr)]
       [_ #f])]
    [`(existsE (,x ,y) ,p ,q)
      (match (synthJ env p)
        [`((exists ,z ,r) true)
          (synthJ
            (dict-set (dict-set env x 'sexpr) y `(,(subst/prop r z x) true))
            q)]
        [_ #f])]
    [_ #f]))

(define/contract (alpha-equiv/judgement? j k [j-env (hash)] [k-env (hash)])
  (->* (judgement? judgement?) (dict? dict?) boolean?)
  (match* (j k)
    [(`(,p true) `(,q true))
     (alpha-equiv/prop? p q j-env k-env)]
    [(`(,p prop) `(,q prop))
     (alpha-equiv/prop? p q j-env k-env)]
    [(`(,a sexpr) `(,b sexpr))
     (alpha-equiv/sexpr? a b j-env k-env)]
    [(_ _) #f]))

(define/contract (alpha-equiv/prop? p q [p-env (hash)] [q-env (hash)])
  (->* (prop? prop?) (dict? dict?) boolean?)
  (match* (p q)
    [((? symbol? x) (? symbol? y))
     (symbol=? (dict-ref p-env x x) (dict-ref q-env y y))]
    [(`(= ,a1 ,a2) `(= ,b1 ,b2))
     (and
       (alpha-equiv/sexpr? a1 b1 p-env q-env)
       (alpha-equiv/sexpr? a2 b2 p-env q-env))]
    [(`(exists ,x ,p) `(exists ,y ,q))
     (let ([z (gensym)])
       (alpha-equiv/prop? p q (dict-set p-env x z) (dict-set q-env y z)))]
    [(_ _) #f]))

(define/contract (alpha-equiv/sexpr? a b [a-env (hash)] [b-env (hash)])
  (->* (sexpr? sexpr?) (dict? dict?) boolean?)
  (match* (a b)
    [((? symbol? x) (? symbol? y))
     (symbol=? (dict-ref a-env x x) (dict-ref b-env y y))]))

(define/contract (subst/prop p x e)
  (-> prop? symbol? sexpr? prop?)
  (match p
    [(? symbol? y) y]
    [`(= ,a ,b)
     `(= ,(subst/sexpr a x e) ,(subst/sexpr b x e))]
    [`(exists ,y ,b)
      (let
        ([fresh-y (gensym y)])
        `(exists ,fresh-y ,(subst/prop (subst/prop b y fresh-y) x e)))]))

(define/contract (subst/sexpr a x b)
  (-> sexpr? symbol? sexpr? sexpr?)
  (match a
    [(? symbol? y) #:when (symbol=? x y)
     b]
    [(? symbol? y) y]))

(define default-env
  (hash
    'exists-refl '((exists x (= x x)) true)))

(define default-realizer-env
  (hash
    'exists-refl '(exists (a b) ())))

(define/contract (realizer/proof prf env)
  (-> proof? dict? any/c)
  (match prf
    [(? symbol? x)
     (dict-ref env x)]
    [`(existsI ,a ,p)
     `(exists ,(realizer/sexpr a env) ,(realizer/proof p env))]
    [`(existsE (,x ,x-prf) ,a ,b)
      (match (realizer/proof a env)
        [`(exists ,x-v ,x-prf-v)
          (realizer/proof
            b
            (dict-set (dict-set env x x-v) x-prf x-prf-v))])]))

(define/contract (realizer/sexpr e env)
  (-> sexpr? dict? any/c)
  (match e
    [(? symbol? x) (dict-ref env x)]))

(define prf
  '(existsE (x x-refl) exists-refl
     (existsI x (existsI x x-refl))))

(checkJ
  default-env
  prf
  '((exists x (exists y (= x x))) true))

(realizer/proof prf default-realizer-env)
