#lang racket

(require
  racket/syntax
  racket/trace
  syntax/id-table
  racket/generic
  "pp-srcloc.rkt"
  "monads.rkt")
(provide (all-defined-out))

(struct stx (loc))
(define stx/c (struct/c stx srcloc?))

(struct sexpr ()
  #:methods gen:custom-write
  [(define (write-proc e port mode)
     (write-string "sexpr" port))])
(struct prop ()
  #:methods gen:custom-write
  [(define (write-proc e port mode)
     (write-string "prop" port))])
(struct fun (d c)
  #:methods gen:custom-write
  ;; TODO: Respect mode here
  [(define/generic ^write-proc write-proc)
   (define (write-proc e port mode)
     (match e
       [(fun d c)
        (write-string "(=> " port)
        (^write-proc d port mode)
        (write-string " " port)
        (^write-proc c port mode)
        (write-string ")" port)]))])
(define type/c
  (flat-rec-contract type/c
    (struct/c sexpr)
    (struct/c prop)
    (struct/c fun type/c type/c)))

(struct sexpr/stx stx ())
(struct prop/stx stx ())
(struct fun/stx stx (d c))

(struct static-error (loc))

(define/contract (format-static-error err fmt . vals)
  (->* ((struct/c static-error srcloc?) string?) #:rest any/c string?)
  (match err
    [(static-error loc)
     (format "~a: ~a~n~a"
       (srcloc->string loc)
       (apply format fmt vals)
       (pp-srcloc loc))]))

(struct not-a-type static-error ())

(define wf-type-error/c
  (struct/c not-a-type srcloc?))

(define/contract (raise-wf-type-error e)
  (-> wf-type-error/c none/c)
  (match e
    [(not-a-type loc) (raise-user-error (format-static-error e "not a type"))]))

(define/contract (wf-type s)
  (-> stx/c (err/c wf-type-error/c type/c))
  (match s
    [(sexpr/stx _) (return/err (sexpr))]
    [(prop/stx _) (return/err (prop))]
    [(fun/stx _ d-stx c-stx)
      (do/err
        d <- (wf-type d-stx)
        c <- (wf-type c-stx)
        (return/err (fun d c)))]
    [(stx loc) (raise/err (not-a-type loc))]))

(define/contract (type=? t u)
  (-> type/c type/c boolean?)
  (match* (t u)
    [((sexpr) (sexpr)) #t]
    [((prop) (prop)) #t]
    [((fun d-t c-t) (fun d-u c-u))
      (and (type=? d-t d-u) (type=? c-t c-u))]
    [(_ _) #f]))

(struct lam/stx stx (x b))
(struct var/stx stx (x))
(struct sym/stx stx (s))
(struct con/stx stx (c))
(struct equ/stx stx (t))
(struct all/stx stx (t))
(struct exi/stx stx (t))
(struct app/stx stx (f a))
(struct ann/stx stx (e t))
(struct hole/stx stx ())

(struct lam (x b)
  #:methods gen:custom-write
  [(define (write-proc e port mode)
     (match e
       [(lam x a) (fprintf port "(λ ~a ~a)" (syntax-e x) a)]))])
(struct vbl (x)
  #:methods gen:custom-write
  [(define (write-proc e port mode)
     (match e
       [(vbl x) (fprintf port "~a" (syntax-e x))]))])
(struct sym (s)
  #:methods gen:custom-write
  [(define (write-proc e port mode)
     (match e
       [(sym s) (fprintf port "'~a" s)]))])
(struct con (c)
  #:methods gen:custom-write
  [(define (write-proc e port mode)
     (match e
       [(con s) (fprintf port "~a" s)]))])
(struct equ (t)
  #:methods gen:custom-write
  [(define (write-proc e port mode)
     (match e
       [(equ t) (fprintf port "(= ~a)" t)]))])
(struct all (t)
  #:methods gen:custom-write
  [(define (write-proc e port mode)
     (match e
       [(all t) (fprintf port "(∀ ~a)" t)]))])
(struct exi (t)
  #:methods gen:custom-write
  [(define (write-proc e port mode)
     (match e
       [(exi t) (fprintf port "(∃ ~a)" t)]))])
(struct app (f a)
  #:methods gen:custom-write
  [(define (write-proc e port mode)
     (match e
       [(app f a) (fprintf port "(~a ~a)" f a)]))])
(struct ann (e t)
  #:methods gen:custom-write
  [(define (write-proc e port mode)
     (match e
       [(ann e t) (fprintf port "(the ~a ~a)" t e)]))])

(define (constant? c)
  (set-member? (set `cons `empty `symbol? `-> `and `or `⊤ `⊥) c))

(define/contract (constant-type c)
  (-> constant? type/c)
  (match c
    [`cons (fun (sexpr) (fun (sexpr) (sexpr)))]
    [`empty (sexpr)]
    [`symbol? (fun (sexpr) (prop))]
    [`-> (fun (prop) (fun (prop) (prop)))]
    [`and (fun (prop) (fun (prop) (prop)))]
    [`or (fun (prop) (fun (prop) (prop)))]
    [`⊤ (prop)]
    [`⊥ (prop)]))

(define expr/c
  (flat-rec-contract expr/c
    (struct/c lam identifier? expr/c)
    (struct/c vbl identifier?)
    (struct/c sym symbol?)
    (struct/c con constant?)
    (struct/c equ type/c)
    (struct/c all type/c)
    (struct/c exi type/c)
    (struct/c app expr/c expr/c)
    (struct/c ann expr/c type/c)))

(struct env-val (type value)
  #:methods gen:custom-write
  ;; TODO: Respect mode here
  [(define/generic ^write-proc write-proc)
   (define (write-proc e port mode)
     (match e
       [(env-val t _)
        (write-string ": " port)
        (^write-proc t port mode)]))])

;; A type-env is a dict with identifier? keys and (or/c env-val? any/c) values
;; TODO: Make this proper
(define type-env/c dict?)

(define/contract (type-env->string env)
  (-> type-env/c string?)
  (for/fold
    ([s ""])
    ([(v t) (in-dict env)])
    (format "~a~n~a ~a" s (syntax-e v) t)))

(define/contract ((check/c env t) e)
  (-> type-env/c type/c (-> any/c boolean?))
  (match* (t e)
    [((fun d c) (lam x b))
      ((check/c (dict-set env x (env-val d (vbl x))) c) b)]
    [(t e)
      (do/or-false
        s <- ((synth/c env) e)
        (return/or-false (type=? t s)))]))

(define/contract ((synth/c env) e)
  (-> type-env/c (-> any/c (or/c type/c #f)))
  (match e
    [(vbl (? identifier? x))
      (match (dict-ref env x #f)
        [(env-val t _) t]
        [_ #f])]
    [(sym (? symbol?)) (sexpr)]
    [(con (? constant? c)) (constant-type c)]
    [(equ (? type/c t)) (fun t (fun t (prop)))]
    [(all (? type/c t)) (fun (fun t (prop)) (prop))]
    [(exi (? type/c t)) (fun (fun t (prop)) (prop))]
    [(ann e (? type/c t))
      (do/or-false
        ((check/c env t) e)
        (return/or-false t))]
    [(app f a)
      (do/or-false
        f-t <- ((synth/c env) f)
        (match f-t
          [(fun d c)
            (do/or-false
              ((check/c env d) a)
              (return/or-false c))]
          [_ #f]))]
    [_ #f]))

(define/contract ((value/c env t) v)
  (-> type-env/c type/c (-> any/c boolean?))
  (match* (t v)
    [((fun d c) (? procedure? f))
      (let ([x (generate-temporary 'x)])
        ((value/c (dict-set env x (env-val d (vbl x))) c) (f (vbl x))))]
    [(t n)
     (do/or-false
       s <- ((neu/c env) n)
       (return/or-false (type=? t s)))]))

(define/contract ((neu/c env) n)
  (-> type-env/c (-> any/c (or/c type/c #f)))
  (match n
    [(vbl x)
      (match (dict-ref env x #f)
        [(env-val t (vbl (? identifier? y)))
         (and (free-identifier=? x y) t)]
        [_ #f])]
    [(sym _) (sexpr)]
    [(con c) (constant-type c)]
    [(equ t) (fun t (fun t (prop)))]
    [(all t) (fun (fun t (prop)) (prop))]
    [(exi t) (fun (fun t (prop)) (prop))]
    [(app f a)
      (do/or-false
        f-t <- ((neu/c env) f)
        (match f-t
          [(fun d c)
            (do/or-false
              ((value/c env d) a)
              (return/or-false c))]
          [_ #f]))]
    [_ #f]))

(struct env-eval (value))

(define/contract (eval/check env t e)
  (->i
    ([env type-env/c]
     [t (env) type/c]
     [e (env t) (check/c env t)])
    [v (env t e) (value/c env t)])
  (eval/expr env e))

(define (eval/expr env e)
  ;; type-env/c (check/c env t) -> (value/c env t)
  (match e
    [(lam x b)
     (λ (x-v) (eval/expr (dict-set env x (env-eval x-v)) b))]
    [(app f a) (do-app (eval/expr env f) (eval/expr env a))]
    [(ann e _) (eval/expr env e)]
    [(vbl x)
      (match (dict-ref env x)
        [(env-val _ v) v]
        [(env-eval v) v])]
    [n n]))

(define (do-app f a)
  ;; (value/c env (fun d c)) (value/c env d) -> (value/c env c)
  (match f
    [(? procedure? f) (f a)]
    [f (app f a)]))

(define (value=? a b)
  ;; (value/c env t) (value/c env t) -> boolean?
  (match* (a b)
    [((? procedure? f) g)
     (let ([x (generate-temporary 'x)])
       (value=? (do-app f (vbl x)) (do-app g (vbl x))))]
    [(f (? procedure? g))
     (let ([x (generate-temporary 'x)])
       (value=? (do-app f (vbl x)) (do-app g (vbl x))))]
    [((vbl x) (vbl y)) (free-identifier=? x y)]
    [((sym s) (sym t)) (symbol=? s t)]
    [((con c) (con d)) (symbol=? c d)]
    [((equ _) (equ _)) #t]
    [((all _) (all _)) #t]
    [((exi _) (exi _)) #t]
    [((app f a) (app g b))
     (and (value=? f g) (value=? a b))]
    [(_ _) #f]))

(define (quote/value v)
  (match v
    [(? procedure? f)
     (let ([x (generate-temporary 'x)])
       (lam x (quote/value (f (vbl x)))))]
    [(app f a)
     (app (quote/value f) (quote/value a))]
    [n n]))

(struct expected-but-has static-error (expected has))
(struct expected-identifier static-error ())
(struct expected-symbol static-error ())
(struct expected-constant static-error ())
(struct unbound-variable static-error ())
(struct expected-non-function static-error (expected))
(struct expected-function static-error (has))
(struct cannot-synth static-error ())
(struct invalid-expr static-error ())
(struct hole-check-type static-error (env expected))
(struct hole-synth-type static-error (env))
(struct non-expr-variable static-error (x x-env))

(define type-error/c
  (or/c
    wf-type-error/c
    (struct/c expected-but-has srcloc? type/c type/c)
    (struct/c expected-identifier srcloc?)
    (struct/c expected-symbol srcloc?)
    (struct/c expected-constant srcloc?)
    (struct/c unbound-variable srcloc?)
    (struct/c expected-non-function srcloc? type/c)
    (struct/c expected-function srcloc? type/c)
    (struct/c cannot-synth srcloc?)
    (struct/c invalid-expr srcloc?)
    (struct/c hole-check-type srcloc? type-env/c type/c)
    (struct/c hole-synth-type srcloc? type-env/c)
    (struct/c non-expr-variable srcloc? identifier? any/c)))

(define/contract (raise-type-error e)
  (-> type-error/c none/c)
  (match e
    [(expected-but-has loc expected has)
      (raise-user-error
        (format-static-error e "expected expression of type ~a, but has type ~a"
          expected
          has))]
    [(expected-identifier loc)
      (raise-user-error (format-static-error e "expected an identifier"))]
    [(expected-symbol loc)
      (raise-user-error (format-static-error e "expected a symbol"))]
    [(expected-constant loc)
      (raise-user-error (format-static-error e "expected a constant"))]
    [(unbound-variable loc) (raise-user-error (format-static-error e "unbound variable"))]
    [(expected-non-function loc expected)
      (raise-user-error
        (format-static-error e "expected expression of type ~a, but found a function" expected))]
    [(expected-function loc has)
      (raise-user-error
        (format-static-error e "expected an expression of function type, but has type ~a" has))]
    [(cannot-synth loc)
      (raise-user-error (format-static-error e "cannot synthesize a type"))]
    [(invalid-expr loc)
      (raise-user-error (format-static-error e "invalid expression"))]
    [(hole-check-type loc env expected)
      (raise-user-error
        (format "~a~nBindings in scope:~a"
          (format-static-error e "found hole with expected type ~a" expected)
          (type-env->string env)))]
    [(hole-synth-type loc env)
      (raise-user-error
        (format "~a~nBindings in scope:~a"
          (format-static-error e "found hole")
          (type-env->string env)))]
    [(non-expr-variable loc x x-env)
     (raise-user-error (format-static-error e "variable ~a is not an expressions. ~a ~a" (syntax-e x) (syntax-e x) x-env))]
    [e (raise-wf-type-error e)]))

(define/contract (check-type env e t)
  (->i
    ([env type-env/c]
     [e stx/c]
     [t type/c])
    [result (env e t) (err/c type-error/c (check/c env t))])
  (match* (e t)
    [((lam/stx _ x b-stx) (fun d c))
      (do/err
        b <- (check-type (dict-set env x (env-val d (vbl x))) b-stx c)
        (return/err (lam x b)))]
    [((lam/stx loc _ _) t)
      (raise/err (expected-non-function loc t))]
    [((hole/stx loc) t)
      (raise/err (hole-check-type loc env t))]
    [(e-stx t)
      (do/err
        (cons s e) <- (synth-type env e-stx)
        (if (type=? s t)
          (return/err e)
          (raise/err (expected-but-has (stx-loc e-stx) t s))))]))

(define/contract (synth-type env e)
  (->i
    ([env type-env/c]
     [e stx/c])
    [result (env e)
      (err/c
        type-error/c
        (cons/dc [t type/c] [e (t) (check/c env t)]))])
  (match e
    [(var/stx loc (? identifier? x))
      (match (dict-ref env x #f)
        [(env-val t _)
         (return/err (cons t (vbl x)))]
        [#f
         (raise/err (unbound-variable loc))]
        [v
         (raise/err (non-expr-variable loc x v))])]
     [(hole/stx loc)
       (raise/err (hole-synth-type loc env))]
    [(sym/stx loc s)
      (cond
        [(not (symbol? s))
          (raise/err (expected-symbol loc))]
        [else
          (return/err (cons (sexpr) (sym s)))])]
    [(con/stx loc c)
      (cond
        [(not (constant? c))
          (raise/err (expected-constant loc))]
        [else
          (return/err (cons (constant-type c) (con c)))])]
    [(equ/stx _ t-stx)
      (do/err
        t <- (wf-type t-stx)
        let type = (fun t (fun t (prop)))
        (return/err (cons type (equ t))))]
    [(all/stx _ t-stx)
      (do/err
        t <- (wf-type t-stx)
        let type = (fun (fun t (prop)) (prop))
        (return/err (cons type(all t))))]
    [(exi/stx _ t-stx)
      (do/err
        t <- (wf-type t-stx)
        let type = (fun (fun t (prop)) (prop))
        (return/err (cons type(exi t))))]
    [(app/stx _ f-stx a-stx)
      (do/err
        (cons f-t f) <- (synth-type env f-stx)
        (match f-t
          [(fun d c)
            (do/err
              a <- (check-type env a-stx d)
              (return/err (cons c (app f a))))]
          [f-t
            (raise/err (expected-function (stx-loc f-stx) f-t))]))]
    [(ann/stx _ e-stx t-stx)
      (do/err
        t <- (wf-type t-stx)
        e <- (check-type env e-stx t)
        (return/err (cons t (ann e t))))]
    [(lam/stx loc _ _)
      (raise/err (cannot-synth loc))]
    [(stx loc)
      (raise/err (invalid-expr loc))]))

(struct ∀I/stx stx (x x-proof))
(struct ∀E/stx stx (∀-proof expr))
(struct ∃I/stx stx (witness witness-proof))
(struct ∃E/stx stx (∃-proof x-witness x-proof body-proof))
(struct =I/stx stx ()) ;; Refl
(struct =E/stx stx (=-proof prop prop-a))
(struct ->I/stx stx (x prf))
(struct andI/stx stx (a-prf b-prf))
(struct ind-sexpr/stx stx (prop empty-prf symbol-prf cons-prf))

(struct ∀I (x x-proof)
  #:methods gen:custom-write
  [(define (write-proc e port mode)
     (match e
       [(∀I x prf) (fprintf port "(∀I ~a ~a)" (syntax-e x) prf)]))])
(struct ∀E (∀-proof expr))
(struct ∃I (witness witness-proof))
(struct ∃E (∃-proof x-witness x-proof body-proof))
(struct =I ()) ;; Refl
(struct =E (=-proof prop proof-a))
(struct ->I (x prf))
(struct andI (a-prf b-prf))
(struct ind-sexpr (prop empty-prf symbol-prf cons-prf)
  #:methods gen:custom-write
  [(define (write-proc e port mode)
     (match e
       [(ind-sexpr p empty-prf symbol-prf cons-prf) (fprintf port "(ind-sexpr ~a ~a ~a ~a)" p empty-prf symbol-prf cons-prf)]))])

(define proof/c
  (flat-rec-contract proof/c
    (struct/c ∀I identifier? proof/c)
    (struct/c ∀E proof/c expr/c)
    (struct/c ∃I expr/c proof/c)
    (struct/c ∃E proof/c identifier? identifier? proof/c)
    (struct/c =I)
    (struct/c =E proof/c expr/c proof/c)
    (struct/c ->I identifier? proof/c)
    (struct/c andI proof/c proof/c)
    (struct/c ind-sexpr expr/c proof/c proof/c proof/c)))

(struct env-prf (prop)
  #:methods gen:custom-write
  ;; TODO: Respect mode here
  [(define/generic ^write-proc write-proc)
   (define (write-proc e port mode)
     (match e
       [(env-prf p)
        (write-string ":: " port)
        (^write-proc p port mode)]))])

;; A proof-env is a dict with identifier? keys and (or/c env-val? env-thm? any/c) values
;; TODO: Make this proper
(define proof-env/c dict?)

(struct doesnt-prove static-error (prop))
(struct objs-not-equal static-error (a b prop))
(struct hole-check-proof static-error (env prop))
(struct expected-but-proves static-error (expected proves))
(struct invalid-proof static-error ())

(define proof-error/c
  (or/c
    type-error/c
    (struct/c doesnt-prove srcloc? any/c #|(value/c env (prop))|#)
    (struct/c objs-not-equal srcloc? any/c any/c #|(value/c env t)|# any/c #|(value/c env (prop))|#)
    (struct/c hole-check-proof srcloc? type-env/c any/c #|(value/c env (prop))|#)
    (struct/c expected-but-proves srcloc? any/c any/c #|(value/c env (prop))|#)
    (struct/c invalid-proof srcloc?)))

(define/contract (raise-proof-error e)
  (-> proof-error/c none/c)
  (match e
    [(doesnt-prove loc p)
     (raise-user-error (format-static-error e "proof doesn't prove proposition ~a" p))]
    [(objs-not-equal loc a b p)
     (raise-user-error (format-static-error e "failed to prove ~a since ~a and ~a are not equal" p a b))]
    [(hole-check-proof loc env prop)
      (raise-user-error
        (format "~a~nBindings in scope:~a"
          (format-static-error e "found hole when trying to prove ~a" (quote/value prop))
          (type-env->string env)))]
    [(expected-but-proves loc expected proves)
     (raise-user-error (format-static-error e "expected a proof of ~a, but instead proves ~a" (quote/value expected) (quote/value proves)))]
    [(invalid-proof loc)
     (raise-user-error (format-static-error e "invalid proof"))]
    [e (raise-type-error e)]))

(define/contract ((proves-check/c env p) proof)
  (->i
    ([env proof-env/c]
     [p (env) (value/c env (prop))])
    [result (env p) (-> any/c boolean?)])
  (match* (proof p)
    [((∀I x proof) (app (all t) p))
     ((proves-check/c (dict-set env x (env-val t (vbl x))) (do-app p (vbl x))) proof)]
    [((∃I w proof) (app (exi t) p))
     (and
       ((check/c env t) w)
       ((proves-check/c env (do-app p w)) proof))]
    [((=I) (app (app (equ t) a) b))
     (value=? a b)]
    [((->I x prf) (app (app (con '->) a) b))
     ((proves-check/c (dict-set env x (env-prf a)) b) prf)]
    [((andI a-prf b-prf) (app (app (con 'and) a) b))
     (and ((proves-check/c env a) a-prf) ((proves-check/c env b) b-prf))]
    [(prf p)
     (do/or-false
       q <- ((proves-synth/c env) prf)
       (value=? p q))]))

(define/contract ((proves-synth/c env) prf)
  (->i
    ([env proof-env/c])
    [res (env)
      (->i
        ([prf any/c])
        [res (prf) (or/c #f (value/c env (prop)))])])
  (match prf
    [(vbl (? identifier? x))
     (match (dict-ref env x #f)
       [(env-prf p) p]
       [_ #f])]
    [(ind-sexpr p empty-prf symbol-prf cons-prf)
     (do/or-false
       ((check/c env (fun (sexpr) (prop))) p)
       let p-v = (eval/check env (fun (sexpr) (prop)) p)
       ((proves-check/c env (do-app p-v (con 'empty))) empty-prf)
       ((proves-check/c env (app (all (sexpr)) (λ (s) (app (app (con '->) (app (con 'symbol?) s)) (do-app p-v s))))) symbol-prf)
       ((proves-check/c env
          (app (all (sexpr))
            (λ (a) (app (all (sexpr))
              (λ (b)
                (app (app (con '->) (app (app (con 'and) (do-app p-v a)) (do-app p-v b)))
                  (do-app p-v (app (app (con 'cons) a) b))))))))
        cons-prf)
       (return/or-false (app (all (sexpr)) (λ (s) (do-app p-v s)))))]
    [_ #f]))

(define/contract (check-proof env prf p)
  (->i
    ([env proof-env/c]
     [prf stx/c]
     [p (env) (value/c env (prop))])
    [res (env prf p) (err/c proof-error/c (proves-check/c env p))])
  (match* (prf p)
    [((∀I/stx _ x prf-stx) (app (all t) p))
     (do/err
       prf <- (check-proof (dict-set env x (env-val t (vbl x))) prf-stx (do-app p (vbl x)))
       (return/err (∀I x prf)))]
    [((∀I/stx loc _ _) p)
     (raise/err (doesnt-prove loc p))]
    [((∃I/stx loc w-stx prf-stx) (app (exi t) p))
     (do/err
       w <- (check-type env w-stx t)
       let w-v = (eval/check env t w)
       prf <- (check-proof env prf-stx (do-app p w-v))
       (return/err (∃I w prf)))]
    [((∃I/stx loc _ _) p)
     (raise/err (doesnt-prove loc p))]
    [((=I/stx loc) (app (app (equ t) a) b))
     (if (value=? a b)
       (return/err (=I))
       (raise/err (objs-not-equal loc a b p)))]
    [((=I/stx loc) p)
     (raise/err (doesnt-prove loc p))]
    [((->I/stx loc (? identifier? x) prf-stx) (app (app (con '->) d) c))
     (do/err
       prf <- (check-proof (dict-set env x (env-prf d)) prf-stx c)
       (return/err (->I x prf)))]
    [((->I/stx loc (? identifier? _) _) p)
     (raise/err (doesnt-prove loc p))]
    [((andI/stx _ a-prf-stx b-prf-stx) (app (app (con 'and) a) b))
     (do/err
       a-prf <- (check-proof env a-prf-stx a)
       b-prf <- (check-proof env b-prf-stx b)
       (return/err (andI a-prf b-prf)))]
    [((andI/stx loc _ _) p)
     (raise/err (doesnt-prove loc p))]
    [((hole/stx loc) p)
     (raise/err (hole-check-proof loc env p))]
    [(prf-stx p)
     (do/err
       (cons q prf) <- (synth-proof env prf-stx)
       (if (value=? p q)
         (return/err prf)
         (raise/err (expected-but-proves (stx-loc prf-stx) p q))))]))

(define/contract (synth-proof env prf)
  (->i
    ([env type-env/c]
     [e stx/c])
    [result (env e)
      (err/c
        proof-error/c
        (cons/dc [p (value/c env (prop))] [e (p) (proves-check/c env p)]))])
  (match prf
    [(var/stx loc (? identifier? x))
     (match (dict-ref env x #f)
       [(env-prf p) (return/err (cons p (vbl x)))])]
    [(ind-sexpr/stx loc p-stx empty-prf-stx symbol-prf-stx cons-prf-stx)
     (do/err
       p <- (check-type env p-stx (fun (sexpr) (prop)))
       let p-v = (eval/check env (fun (sexpr) (prop)) p)
       empty-prf <- (check-proof env empty-prf-stx (do-app p-v (con 'empty)))
       symbol-prf <- (check-proof env symbol-prf-stx (app (all (sexpr)) (λ (s) (app (app (con '->) (app (con 'symbol?) s)) (do-app p-v s)))))
       cons-prf <-
         (check-proof
           env
           cons-prf-stx
           (app (all (sexpr))
             (λ (a) (app (all (sexpr))
               (λ (b)
                 (app (app (con '->) (app (app (con 'and) (do-app p-v a)) (do-app p-v b)))
                   (do-app p-v (app (app (con 'cons) a) b))))))))
       (return/err
         (cons
           (app (all (sexpr)) (λ (s) (do-app p-v s)))
           (ind-sexpr p empty-prf symbol-prf cons-prf))))]
    [(stx loc)
     (raise/err (invalid-proof loc))]))

(struct def/stx stx (x t e))
(struct def-prf/stx stx (x p e))

(struct def (x t e))
(struct def-prf (x p e))

(define module-def/c
  (or/c
    (struct/c def identifier? type/c expr/c)
    (struct/c def-prf identifier? expr/c proof/c)))

(struct invalid-module-def static-error ())
(struct multiple-definition-for-name static-error ())

(define wf-module-def-error/c
  (or/c
    type-error/c
    proof-error/c
    (struct/c invalid-module-def srcloc?)
    (struct/c multiple-definition-for-name srcloc?)))

(define/contract (raise-wf-module-def-error e)
  (-> wf-module-def-error/c none/c)
  (match e
    [(invalid-module-def loc)
      (raise-user-error (format-static-error e "invalid module-level definition"))]
    [(multiple-definition-for-name loc)
      (raise-user-error (format-static-error e "a top-level binding for this name already exists"))]
    [e (raise-proof-error e)]))

(define/contract (wf-module-def env d)
  (-> type-env/c stx/c (err/c wf-module-def-error/c module-def/c))
  (match d
    [(def/stx loc x _ _) #:when (dict-has-key? env x)
     (raise/err (multiple-definition-for-name loc))]
    [(def/stx loc x t-stx e-stx)
     (do/err
       t <- (wf-type t-stx)
       e <- (check-type env e-stx t)
       (return/err (def x t e)))]
    [(def-prf/stx loc x _ _) #:when (dict-has-key? env x)
     (raise/err (multiple-definition-for-name loc))]
    [(def-prf/stx loc x p-stx prf-stx)
     (do/err
       p <- (check-type env p-stx (prop))
       let p-v = (eval/check env (prop) p)
       prf <- (check-proof env prf-stx p-v)
       (return/err (def-prf x p prf)))]
    [(stx loc)
      (raise/err (invalid-module-def loc))]))

(define wf-module-error/c
  wf-module-def-error/c)

(define/contract (raise-wf-module-error e)
  (-> wf-module-error/c none/c)
  (raise-wf-module-def-error e))

(define/contract (wf-module m)
  (-> (listof stx/c) (err/c wf-module-error/c (listof module-def/c)))
  (let loop
    ([env (make-immutable-free-id-table)]
     [defs `()]
     [m m])
    (match m
      [`() (return/err defs)]
      [`(,def-stx ,defs-stx ...)
        (do/err
          d <- (wf-module-def env def-stx)
          (match d
            [(def x t e)
             (loop
               (dict-set env x (env-val t (eval/check env t e)))
               (append defs (list d))
               defs-stx)]
            [(def-prf x p prf)
             (loop
               (dict-set env x (env-prf p))
               (append defs (list d))
               defs-stx)]))])))
