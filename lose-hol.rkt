#lang racket

(require
  racket/syntax
  racket/trace
  syntax/id-table
  racket/generic
  "pp-srcloc.rkt"
  "monads.rkt")
(provide (all-defined-out))

;; type ::=
;;   | `sexpr
;;   | `prop
;;   | `(fun ,type ,type)
;;
;; x ::= variable?
;;
;; expr ::=
;;   | check
;;   | synth
;;
;; check ::=
;;   | `(λ ,x ,expr)
;;
;; synth ::=
;;   | x
;;   | `cons
;;   | `(quote ,symbol?)
;;   | `()
;;   | `symbol?
;;   | `(= ,type)
;;   | `(∀ ,type)
;;   | `(∃ ,type)
;;   | `->
;;   | `and
;;   | `or
;;   | `⊤
;;   | `⊥
;;   | `(,synth ,expr)

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

(struct lam (x b))
(struct vbl (x))
(struct sym (s))
(struct con (c))
(struct equ (t))
(struct all (t))
(struct exi (t))
(struct app (f a))
(struct ann (e t))

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

(struct env-def (type value)
  #:methods gen:custom-write
  ;; TODO: Respect mode here
  [(define/generic ^write-proc write-proc)
   (define (write-proc e port mode)
     (match e
       [(env-def t _)
        (write-string ": " port)
        (^write-proc t port mode)]))])
;; TODO: Consider making just using env-def bound to the variable itself instead
;;   Would act sort of like a substitution then?
(struct env-param (type)
  #:methods gen:custom-write
  ;; TODO: Respect mode here
  [(define/generic ^write-proc write-proc)
   (define (write-proc e port mode)
     (match e
       [(env-param t)
        (write-string ": " port)
        (^write-proc t port mode)]))])
;; A type-env is a dict with identifier? keys and (or/c env-def? env-param? any/c) values
;; TODO: Make this proper
(define type-env/c dict?)

(define/contract (type-env->string env)
  (-> type-env/c string?)
  (for/fold
    ([s ""])
    ([(v t) (in-dict env)])
    (format "~a~n~a ~a" s (identifier-binding-symbol v) t)))

(define/contract ((canonical/c env type) expr)
  (-> type-env/c type/c (-> any/c boolean?))
  (match* (expr type)
    [((lam (? identifier? x) b) (fun d c))
      ((canonical/c (dict-set env x (env-param d)) c) b)]
    [(expr (or (sexpr) (prop)))
      (do/or-false
        s <- ((atomic/c env) expr)
        (return/or-false (type=? s type)))]
    [(_ _) #f]))

(define/contract ((atomic/c env) expr)
  (-> type-env/c (-> any/c (or/c #f type/c)))
  (match expr
    [(vbl x)
      (match (dict-ref env x #f)
       [(env-param t) t]
       [_ #f])]
    [(sym _) (sexpr)]
    [(con c) (constant-type c)]
    [(equ t) (fun t (fun t (prop)))]
    [(all t) (fun (fun t (prop)) (prop))]
    [(exi t) (fun (fun t (prop)) (prop))]
    [(app f a)
      (do/or-false
        t <- ((atomic/c env) f)
        (match t
          [(fun d c)
            (do/or-false
              ((canonical/c env d) a)
              (return/or-false c))]
          [_ #f]))]
    [_ #f]))

(define (canonical=? a b)
  ;; (canonical/c env a) (canonical/c env a) -> boolean?
  (define (canonical=? l env-a env-b a b)
    ;; natural? (dictof identifier? natural?) (canonical/c env a) (canonical/c env a) -> boolean?
    (match* (a b)
      [((lam x a) (lam y b))
        (canonical=?
          (+ l 1)
          (dict-set env-a x l)
          (dict-set env-b y l)
          a
          b)]
      [((lam _ _) _) #f]
      [(_ (lam _ _)) #f]
      [(a b) (atomic=? l env-a env-b a b)]))
  (define (atomic=? l env-a env-b a b)
    (match* (a b)
      [((vbl x) (vbl y)) #:when (and (dict-has-key? env-a x) (dict-has-key? env-b y))
       (= (dict-ref env-a x) (dict-ref env-b y))]
      [((vbl x) (vbl y)) (free-identifier=? x y)]
      [((sym s) (sym t)) (symbol=? s t)]
      [((con c) (con d)) (symbol=? c d)]
      [((equ _) (equ _)) #t]
      [((all _) (all _)) #t]
      [((exi _) (exi _)) #t]
      [((app f a) (app g b))
        (and
          (atomic=? l env-a env-b f g)
          (canonical=? l env-a env-b a b))]
      [(_ _) #f]))
  (canonical=? 0 (make-immutable-free-id-table) (make-immutable-free-id-table) a b))

(define (do-app f a)
  ;; (canonical/c env (fun d c)) (canonical/c env d) -> (canonical/c env c)
  (match f
    [(lam x b) (hereditary-subst/n b x a)]))

(define (head-identifier=? a x)
  ;; (atomic/c env a) identifier? -> boolean?
  (match a
    [(app f _) (head-identifier=? f x)]
    [(vbl y) (free-identifier=? x y)]
    [_ #f]))

(define (eta-expand t a)
  ;; (t : type/c) (atomic/c env t) -> (canonical/c env t)
  (match t
    [(fun d c)
     (let ([x (generate-temporary 'x)])
       (lam x (eta-expand c (app a (eta-expand d x)))))]
    [t a]))

;; a[x := v]
(define (hereditary-subst/n a x v)
  ;; (canonical/c env a) identifier? (canonical/c env b) -> (canonical/c env a)
  (match a
    [(lam y b)
     (lam y (hereditary-subst/n b x v))]
    [a #:when (head-identifier=? a x)
     (hereditary-subst/rn a x v)]
    [a
     (hereditary-subst/rr a x v)]))

(define (hereditary-subst/rn a x v)
  ;; (head-identifier=? a x) must be true
  ;; (atomic/c env a) identifier? (canonical/c env b) -> (canonical/c env a)
  (match a
    ;; These are the only two cases since we assume (head-identifier=? a x is true)
    [(vbl _) v] ;; Since we assume (head-identifier=? a x) is true, this must be x
    [(app f a)
      (do-app (hereditary-subst/rn f x v) (hereditary-subst/n a x v))]))

(define (hereditary-subst/rr a x v)
  ;; (head-identifier=? a x) must be false
  ;; (atomic/c env a) identifier? (canonical/c env b) -> (atomic/c env a)
  (match a
    [(app f a)
     (app (hereditary-subst/rr f x v) (hereditary-subst/n a x v))]
    [a a]))

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
    (struct/c hole-synth-type srcloc? type-env/c)))

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
    [e (raise-wf-type-error e)]))



(define/contract (check-type env e t)
  (->i
    ([env type-env/c]
     [e stx/c]
     [t type/c])
    [result (env e t) (err/c type-error/c (canonical/c env t))])
  (match* (e t)
    [((lam/stx _ x b-stx) (fun d c))
      (do/err
        b <- (check-type (dict-set env x (env-param d)) b-stx c)
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
        (cons/dc [t type/c] [e (t) (canonical/c env t)]))])
  (match e
    [(var/stx loc x)
      (match (dict-ref env x #f)
        [(env-param t)
          (return/err (cons t (eta-expand t (vbl x))))]
        [(env-def t v)
          (return/err (cons t v))]
        [#f (raise/err (unbound-variable loc))])]
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
          (return/err (cons (constant-type c) (eta-expand (constant-type c) (con c))))])]
    [(equ/stx _ t-stx)
      (do/err
        t <- (wf-type t-stx)
        let type = (fun t (fun t (prop)))
        (return/err (cons type (eta-expand type (equ t)))))]
    [(all/stx _ t-stx)
      (do/err
        t <- (wf-type t-stx)
        let type = (fun (fun t (prop)) (prop))
        (return/err (cons type (eta-expand type (all t)))))]
    [(exi/stx _ t-stx)
      (do/err
        t <- (wf-type t-stx)
        let type = (fun (fun t (prop)) (prop))
        (return/err (cons type (eta-expand type (exi t)))))]
    [(app/stx _ f-stx a-stx)
      (do/err
        (cons f-t f) <- (synth-type env f-stx)
        (match f-t
          [(fun d c)
            (do/err
              a <- (check-type env a-stx d)
              (return/err (cons c (do-app f a))))]
          [f-t
            (raise/err (expected-function (stx-loc f-stx) f-t))]))]
    [(ann/stx _ e-stx t-stx)
      (do/err
        t <- (wf-type t-stx)
        e <- (check-type env e-stx t)
        (return/err (cons t e)))]
    [(lam/stx loc _ _)
      (raise/err (cannot-synth loc))]
    [(stx loc)
      (raise/err (invalid-expr loc))]))

(struct def/stx stx (x t e))

(struct def (x t e))

(define module-def/c
  (struct/c def identifier? type/c expr/c))

(struct invalid-module-def static-error ())
(struct multiple-definition-for-name static-error ())

(define wf-module-def-error/c
  (or/c
    type-error/c
    (struct/c invalid-module-def srcloc?)
    (struct/c multiple-definition-for-name srcloc?)))

(define/contract (raise-wf-module-def-error e)
  (-> wf-module-def-error/c none/c)
  (match e
    [(invalid-module-def loc)
      (raise-user-error (format-static-error e "invalid module-level definition"))]
    [(multiple-definition-for-name loc)
      (raise-user-error (format-static-error e "a top-level binding for this name already exists"))]
    [e (raise-type-error e)]))

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
             (loop (dict-set env x (env-param t)) (append defs (list d)) defs-stx)]))])))

(struct ∀I/stx stx (x x-proof))
(struct ∀E/stx stx (∀-proof expr))
(struct ∃I/stx stx (witness witness-proof))
(struct ∃E/stx stx (∃-proof x-witness x-proof body-proof))
(struct =I/stx stx ()) ;; Refl
(struct =E/stx stx (=-proof prop prop-a))

(struct ∀I (x x-proof))
(struct ∀E (∀-proof expr))
(struct ∃I (witness witness-proof))
(struct ∃E (∃-proof x-witness x-proof body-proof))
(struct =I ()) ;; Refl
(struct =E (=-proof prop prop-a))

(struct env-thm (prop))

;; A proof-env is a dict with identifier? keys and (or/c env-def? env-param? env-thm? any/c) values
;; TODO: Make this proper
(define proof-env/c dict?)

(define/contract ((proves-check/c env p) proof)
  (->i
    ([env proof-env/c]
     [p (env) (canonical/c env (prop))])
    [result (env p) (-> any/c boolean?)])
  (match* (proof p)
    [((∀I x proof) (app (all t) p))
     ((proves-check/c (dict-set env x (env-param t)) (do-app p (vbl x))) proof)]
    [((∃I w proof) (app (exi t) p))
     (and
       ((canonical/c env t) w)
       ((proves-check/c env (do-app p w)) proof))]
    [((=I) (app (app (equ t) a) b))
     (canonical=? a b)]))

#|
(define/contract (subst e x a)
  (-> expr? variable? expr? expr?)
  (match e
    [`(λ ,y ,b)
      (let ([z (gensym)])
        `(λ ,z ,(subst (subst b y z) x a)))]
    [(? variable? y) #:when (symbol=? x y)
      a]
    [(? variable? y) y]
    [`cons e]
    [`(quote ,_) e]
    [`() e]
    [`symbol? e]
    [`pair? e]
    [`empty? e]
    [`(= ,_) e]
    [`(∀ ,_) e]
    [`(∃ ,_) e]
    [`-> e]
    [`and e]
    [`or e]
    [`(,f ,arg)
      (app (subst f x a) (subst arg x a))]))

(define/contract (app f a)
  (-> expr? expr? expr?)
  (match f
    [`(λ ,x ,b)
      (subst b x a)]
    [f `(,f ,a)]))

(define/contract (app* f arg . args)
  (->* (expr? expr?) #:rest expr? expr?)
  (match args
    [`() (app f arg)]
    [`(,next-arg ,args ...)
      (apply app* (app f arg) next-arg args)]))

(define/contract (expr=? a b)
  (-> expr? expr? boolean?)
  (match* (a b)
    [(`(λ ,_ ,_) _)
     (let ([x (gensym)])
       (expr=? (app a x) (app b x)))]
    [(_ `(λ ,_ ,_))
     (let ([x (gensym)])
       (expr=? (app a x) (app b x)))]
    [((? variable? x) (? variable? y)) (symbol=? x y)]
    [(`cons `cons) #t]
    [(`(quote ,s) `(quote ,t))
     (symbol=? s t)]
    [(`() `()) #t]
    [(`symbol? `symbol?) #t]
    [(`pair? `pair?) #t]
    [(`empty? `empty?) #t]
    [(`(= ,t) `(= ,u)) (type=? t u)]
    [(`(= ,t) _) #f]
    [(_ `(= ,u)) #f]
    [(`(∀ ,t) `(∀ ,u)) (type=? t u)]
    [(`(∀ ,t) _) #f]
    [(_ `(∀ ,u)) #f]
    [(`(∃ ,t) `(∃ ,u)) (type=? t u)]
    [(`(∃ ,t) _) #f]
    [(_ `(∃ ,u)) #f]
    [(`-> `->) #t]
    [(`and `and) #t]
    [(`or `or) #t]
    [(`⊤ `⊤) #t]
    [(`⊥ `⊥) #t]
    [(`(,a-f ,a-arg) `(,b-f ,b-arg))
     (and (expr=? a-f b-f) (expr=? a-arg b-arg))]))

;; type-env ::= (dictof symbol? type?)

(define (type-env? env)
  (dict? env))

;;
;; [,type-env |- ,expr : ,t]
;;
;; ,(dict-ref Γ x) = ,t
;; -------------------- var
;; ,Γ |- ,x : ,t
;; 
;;

(define/contract (type-check env e t)
  (-> type-env? expr? type? boolean?)
  (match* (e t)
    [(`(λ ,x ,b) `(fun ,d ,c))
     (type-check (dict-set env x d) b c)]
    [(`(λ ,_ ,_) _) #f]
    [(e t) (equal? t (type-synth env e))]))

(define/contract (type-synth env e)
  (-> type-env? expr? (or/c type? #f))
  (match e
    [(? variable? x) (dict-ref env x #f)]
    [`cons `(fun sexpr (fun sexpr sexpr))]
    [`(quote ,_) `sexpr]
    [`() `sexpr]
    [`symbol? `(fun sexpr prop)]
    [`pair? `(fun sexpr prop)]
    [`empty? `(fun sexpr prop)]
    [`(= ,t) `(fun ,t (fun ,t prop))]
    [`(∀ ,t) `(fun (fun ,t prop) prop)]
    [`(∃ ,t) `(fun (fun ,t prop) prop)]
    [`-> `(fun prop (fun prop prop))]
    [`and `(fun prop (fun prop prop))]
    [`or `(fun prop (fun prop prop))]
    [`⊤ `prop]
    [`⊥ `prop]
    [`(,f ,arg)
      (match (type-synth env f)
        [`(fun ,d ,c)
          (and (type-check env arg d) c)]
        [_ #f])]))

;; proof ::=
;;   | check-proof?
;;   | synth-proof?
;;
;; check-proof? ::=
;;   | (∀I ,variable? ,proof)
;;   | (∃I ,expr ,proof)
;;   | (->I ,variable? ,proof?)
;;   | (andI ,proof ,proof)
;;   | (orI-L ,proof)
;;   | (orI-R ,proof)
;;   | (⊤I)
;;   | _
;;
;; synth-proof? ::=
;;   | variable?
;;   | (ind-sexpr ,expr ,proof ,proof ,proof)
;;   | (∀E ,proof ,expr)
;;   | (∃E (,symbol? ,symbol?) ,proof ,proof)
;;   | (->E ,proof ,proof)
;;   | (andE-L ,proof)
;;   | (andE-R ,proof)
;;   | (orE ,proof (,variable? ,proof) (,variable? ,proof?))
;;   | (⊥E ,expr ,proof)

(define (proof? p)
  (match p
    [(? variable?) #t]
    #;
    [`(ind-sexpr ,prop-expr ,empty-p ,sym-p ,pair-p)
      (and (expr? prop-expr) (proof? empty-p) (proof? sym-p) (proof? pair-p))]
    [`(∀I ,x ,p)
      (and (variable? x) (proof? p))]
    [`(∀E ,p ,e)
      (and (proof? p) (expr? e))]
    [`(∃I ,e ,p)
      (and (expr? e) (proof? p))]
    [`(∃E (,x ,x-prf) ,exists-p ,p)
      (and (variable? x) (variable? x-prf) (proof? exists-p) (proof? p))]
    [`(->I ,x ,p)
      (and (variable? x) (proof? p))]
    [`(->E ,imp-p ,prec-p)
      (and (proof? imp-p) (proof? prec-p))]
    [`(andI ,l-p ,r-p)
      (and (proof? l-p) (proof? r-p))]
    [`(andE-L ,p)
      (proof? p)]
    [`(andE-R ,p)
      (proof? p)]
    [`(orI-L ,p)
      (proof? p)]
    [`(orI-R ,p)
      (proof? p)]
    [`(orE ,or-p (,x ,l-p) (,y ,r-p))
      (and (proof? or-p) (variable? x) (proof? l-p) (variable? y) (proof? r-p))]
    [`(⊤I) #t]
    [`(⊥E ,prop ,p)
      (and (expr? prop) (proof? p))]
    [`(=E ,=prf ,p ,p-a)
      (and (proof? =prf) (expr? p) (proof? p-a))]
    [`_ #t]
    [_ #f]))

;; proof-env ::= (dictof variable? expr?)

(define (proof-env? env)
  (dict? env))

;; [,type-env | ,proof-env |- ,proof : ,expr]
;; 
;; ,(dict-ref Θ x) = ,p
;; -------------------- var
;; ,Γ | ,Θ |- ,x : ,p
;;
;; ,Γ |- ,p : (fun sexpr prop)
;; ,Γ | ,Θ |- ,empty : (,p `())
;; ,Γ | ,Θ |- ,sym : ((∀ sexpr) (λ x (-> (symbol? x) (,p x))))
;; ,Γ | ,Θ |- ,pair : ((∀ sexpr) (λ x ((∀ sexpr) (λ y (-> (and (,p x) (,p y)) (,p (cons ,x ,y)))))))
;; ------------------------------------------- ind-sexpr
;; ,Γ | ,Θ |- (ind-sexpr ,p ,empty ,sym ,pair) : ((∀ sexpr) ,p)
;;
;; ,(dict-set Γ x t) | ,Θ |- ,b : (,p ,x)
;; -------------------------------------- ∀I
;; ,Γ | ,Θ |- (∀I ,x ,b) : ((∀ ,t) ,p)
;;
;; ,Γ | ,Θ |- ,prf : ((∀ ,t) ,p)
;; ,Γ |- ,e : ,t
;; --------------------------------- ∀E
;; ,Γ | ,Θ |- (∀E ,prf ,e) : (,p ,e)
;;
;; ,Γ |- ,e : ,t
;; ,Γ | ,Θ |- ,prf : (,p ,e)
;; -------------------------------------
;; ,Γ | ,Θ |- (∃I ,e ,prf) : ((∃ ,t) ,p)
;;
;; ,Γ | ,Θ |- ,exists-p : ((∃ ,t) ,p)
;; ,(dict-set Γ x t) | ,(dict-set Θ x-prf `(,p ,x)) |- ,b : ,q
;; -----------------------------------------------------------
;; ,Γ | ,Θ |- (∃E (,x ,x-prf) ,exists-p ,b) : ,q

(define/contract (proof-check type-env proof-env prf prop)
  (-> type-env? proof-env? proof? expr? boolean?)
  (match* (prf prop)
    [(`(∀I ,x ,b) `((∀ ,t) ,p))
     (proof-check (dict-set type-env x t) proof-env b (app p x))]
    [(`(∀I ,_ ,_) _) #f]
    [(`(∃I ,e ,prf) `((∃ ,t) ,p))
     (and
       (type-check type-env e t)
       (proof-check type-env proof-env prf (app p e)))]
    [(`(∃I ,_ ,_) _) #f]
    [(`(∃E (,x ,x-p) ,exists-p ,b) prop)
     (match (proof-synth type-env proof-env exists-p)
       [`((∃ ,t) ,p)
         (proof-check (dict-set type-env x t) (dict-set proof-env x-p (app p x)) b prop)]
       [_ #f])]
    [(`(->I ,x ,prf) `((-> ,A) ,B))
     (proof-check type-env (dict-set proof-env x A) prf B)]
    [(`(->I ,_ ,_) _) #f]
    [(`(andI ,a ,b) `((and ,A) ,B))
     (and (proof-check type-env proof-env a A) (proof-check type-env proof-env b B))]
    [(`(orI-L ,a) `((or ,A) ,_))
     (proof-check type-env proof-env a A)]
    [(`(orI-R ,b) `((or ,_) ,B))
     (proof-check type-env proof-env b B)]
    [(`(orE ,or-p (,x ,l-p) (,y ,r-p)) prop)
     (match (proof-synth type-env proof-env or-p)
       [`(or ,A ,B)
         (and
           (proof-check type-env (dict-set proof-env x A) l-p prop)
           (proof-check type-env (dict-set proof-env y B) r-p prop))]
       [_ #f])]
    [(`(⊤I) `⊤) #t]
    [(`(⊤I) _) #f]
    [(`_ prop) (error `proof-hole "~n~a~n~n~a~n~n_ : ~a" (dict->list type-env) (dict->list proof-env) prop)]
    [(prf prop)
     (cond
       [(proof-synth type-env proof-env prf)
        fun
        (λ (synthed-prop) (expr=? prop synthed-prop))]
       [else #f])]))

(define/contract (proof-synth type-env proof-env prf)
  (-> type-env? proof-env? proof? (or/c expr? #f))
  (match prf
    [(? variable? x) (dict-ref proof-env x #f)]
    #;
    [`(ind-sexpr ,p ,empty-p ,sym-p ,pair-p)
      (and 
        (type-check type-env p `(fun sexpr prop))
        (proof-check type-env proof-env empty-p (app p `()))
        (let ([x (gensym)])
          (proof-check type-env proof-env sym-p `((∀ sexpr) (λ ,x ((-> (symbol? ,x)) ,(app p x))))))
        (let ([x (gensym)] [y (gensym)])
          (proof-check type-env proof-env empty-p `((∀ sexpr) (λ ,x ((∀ sexpr) (λ ,y ((-> ((and ,(app p x)) ,(app p y))) ,(app p `((cons ,x) ,y)))))))))
        `((∀ sexpr) ,p))]
    [`(∀E ,forall-p ,e)
      (match (proof-synth type-env proof-env forall-p)
        [`((∀ ,t) ,p)
          (and
            (type-check type-env e t)
            (app p e))]
        [_ #f])]
    [`(∃E (,x ,x-p) ,exists-p ,b)
     (match (proof-synth type-env proof-env exists-p)
       [`((∃ ,t) ,p)
         (proof-synth (dict-set type-env x t) (dict-set proof-env x-p (app p x)) b)]
       [_ #f])]
    [`(->E ,imp-p ,prec-p)
      (match (proof-synth type-env proof-env imp-p)
        [`((-> ,A) ,B)
          (and
            (proof-check type-env proof-env prec-p A)
            B)]
        [_ #f])]
    [`(andE-L ,p)
      (match (proof-synth type-env proof-env p)
        [`((and ,A) ,_) A]
        [_ #f])]
    [`(andE-R ,p)
      (match (proof-synth type-env proof-env p)
        [`((and ,_) ,B) B]
        [_ #f])]
    [`(orE ,or-p (,x ,l-p) (,y ,r-p))
     (match (proof-synth type-env proof-env or-p)
       [`((or ,A) ,B)
         (let
           ([l-prop (proof-synth type-env (dict-set proof-env x A) l-p)]
            [r-prop (proof-synth type-env (dict-set proof-env y B) r-p)])
           (and
             l-prop
             r-prop
             (expr=? l-prop r-prop)
             l-prop))]
       [_ #f])]
    [`(=E ,=prf ,p ,p-a)
      (match (proof-synth type-env proof-env =prf)
        [`(((= ,t) ,a) ,b)
          (and
            (type-check type-env p `(fun ,t prop))
            (proof-check type-env proof-env p-a (app p a))
            (app p b))]
        [_ #f])]
    [`(⊥E ,prop ,p)
      (and
        (type-check type-env prop `prop)
        (proof-check type-env proof-env p `⊥)
        prop)]
    [_ #f]))

(define (realizer-expr-env? env)
  (dict? env))

(define (realizer-proof-env? env)
  (dict? env))

(define/contract (realizer/proof expr-env proof-env prf)
  (-> realizer-expr-env? realizer-proof-env? proof? any/c)
  (match prf
    [`(∀I ,x ,b)
      (λ (x-realizer)
        (realizer/proof (dict-set expr-env x x-realizer) proof-env b))]
    [`(∃I ,e ,b)
      (cons (realizer/expr expr-env e) (realizer/proof expr-env proof-env b))]
    [`(->I ,x ,b)
      (λ (x-realizer)
        (realizer/proof expr-env (dict-set proof-env x x-realizer) b))]
    [`(andI ,a ,b)
      (cons (realizer/proof expr-env proof-env a) (realizer/proof expr-env proof-env b))]
    [`(orI-L ,a)
      `(left ,(realizer/proof expr-env proof-env a))]
    [`(orI-R ,b)
      `(right, (realizer/proof expr-env proof-env b))]
    [(? variable? x)
      (dict-ref proof-env x)]
    #;
    [`(ind-sexpr ,p ,empty-p ,sym-p ,cons-p)
     (let
       ([p-r (realizer/expr expr-env p)]
        [empty-r (realizer/proof expr-env proof-env empty-p)]
        [sym-r (realizer/proof expr-env proof-env sym-p)]
        [cons-r (realizer/proof expr-env proof-env cons-p)])
       (λ (e-r)
         (let loop ([r e-r])
           (match r
             [(? empty?) empty-r]
             [(? symbol? s) ((sym-r s) (void))]
             [(cons a b) (((cons-r a) b) (cons (loop a) (loop b)))]))))]
    [`(∀E ,p ,e)
      ((realizer/proof expr-env proof-env p) (realizer/expr expr-env e))]
    [`(∃E (,x ,x-prf) ,p ,b)
      (match (realizer/proof expr-env proof-env p)
        [(cons e e-r)
         (realizer/proof (dict-set expr-env x e) (dict-set proof-env x-prf e-r) b)])]
    [`(->E ,f ,a)
      ((realizer/proof expr-env proof-env f) (realizer/proof expr-env proof-env a))]
    [`(andE-L ,p)
      (match (realizer/proof expr-env proof-env p)
        [(cons a _) a])]
    [`(andE-R ,p)
      (match (realizer/proof expr-env proof-env p)
        [(cons _ b) b])]
    [`(orE ,p (,x ,p-l) (,y ,p-r))
      (match (realizer/proof expr-env proof-env p)
        [`(left ,l)
          (realizer/proof expr-env (dict-set proof-env x l) p-l)]
        [`(right ,r)
          (realizer/proof expr-env (dict-set proof-env y r) p-r)])]
    [`(⊤I) `()]
    [`(⊥E ,_ ,_) (error "should be impossible")]))

(define/contract (realizer/expr expr-env e)
  (-> realizer-expr-env? expr? any/c)
  (match e
    [`(λ ,x ,b)
      (λ (x-v) (realizer/expr (dict-set expr-env x x-v)))]
    [(? variable? x)
      (dict-ref expr-env x)]
    [`cons
      (λ (a) (λ (b) (cons a b)))]
    [`(quote ,s) s]
    [`() `()]
    [`symbol? (λ (_) (void))]
    [`pair? (λ (_) (void))]
    [`empty? (λ (_) (void))]
    [`(= ,t) (λ (_) (λ (_) (void)))]
    [`(∀ ,t) (λ (_) (λ (_) (void)))]
    [`(∃ ,t) (λ (_) (λ (_) (void)))]
    [`-> (λ (_) (λ (_) (void)))]
    [`and (λ (_) (λ (_) (void)))]
    [`or (λ (_) (λ (_) (void)))]
    [`⊤ (void)]
    [`⊥ (void)]
    [`(,f ,arg ,args ...)
      (let
        ([f-r (realizer/expr expr-env f)]
         [arg-r (realizer/expr expr-env arg)]
         [args-rs (map (λ (arg) (realizer/expr expr-env arg)) args)])
        (let loop ([f f-r] [arg arg-r] [args args-rs])
          (match args
           [`() (f arg)]
           [`(,next-arg ,args ...)
             (loop (f arg) next-arg args)])))]))

(define default-proof-check-env
  (hash
    `sexpr-ind
    `((∀ (fun sexpr prop))
       (λ P
         ((->
           ((and
             (P ()))
             ((and
               ((∀ sexpr) (λ s ((-> (symbol? s)) (P s)))))
               ((∀ sexpr) (λ a ((∀ sexpr) (λ b ((-> ((and (P a)) (P b))) (P ((cons a) b))))))))))
           ((∀ sexpr) (λ a (P a))))))
    `empty-refl `(((= sexpr) ()) ())
    `symbol-refl `((∀ sexpr) (λ s ((-> (symbol? s)) (((= sexpr) s) s))))
    `cons-refl `((∀ sexpr) (λ a ((∀ sexpr) (λ b (((= sexpr) ((cons a) b)) ((cons a) b))))))))

(define default-proof-realizer-env
  (hash
    `sexpr-ind
    (λ (p)
      (λ (cases)
        (λ (e)
          (match e
            [`() (car cases)]
            [(? symbol? s) (((cadr cases) s) (void))]
            [(cons a b) ((((cddr cases) a) b) (cons (void) (void)))]))))
    `empty-refl (void)
    `symbol-refl (λ (s) (λ (s-prf) (void)))))

(module+ test
  (require rackunit)

  (define p0 `((∀ prop) (λ X ((-> X) X))))
  (check-true (expr? p0))
  (check-true (type-check (hash) p0 `prop))

  (define prf0 `(∀I X (->I X-prf X-prf)))
  (check-true (proof? prf0))
  (check-true (proof-check (hash) (hash) prf0 p0))

  (define p1 `((-> ((∃ sexpr) (λ x (((= sexpr) x) x)))) ((∃ sexpr) (λ x (((= sexpr) x) x)))))
  (check-true (expr? p1))
  (check-true (type-check (hash) p0 `prop))

  (define prf1
    `(->I x-exists
       (∃E (x x-refl) x-exists
         (∃I x x-refl))))
  (check-true (proof? prf1))
  (check-true (proof-check (hash) (hash) prf1 p1))

  (check-false (proof-check (hash) (hash) prf0 p1))

  (define r1 (realizer/proof (hash) (hash) prf1))

  (check-equal? (r1 (cons (cons 'a 'b) (void))) (cons (cons 'a 'b) (void)))

  (check-exn exn:fail? (λ () (proof-check (hash) (hash) `_ `⊤)))

  (define sexpr-refl `((∀ sexpr) (λ x (((= sexpr) x) x))))
  (check-true (expr? sexpr-refl))
  (check-true (type-check (hash) sexpr-refl `prop))

  (define sexpr-refl-prf
    `(->E (∀E sexpr-ind (λ e (((= sexpr) e) e))) (andI empty-refl (andI symbol-refl (∀I a (∀I b (->I ab-refl (∀E (∀E cons-refl a) b))))))))
  (check-true (proof? sexpr-refl-prf))
  (check-true (proof-check (hash) default-proof-check-env sexpr-refl-prf sexpr-refl))

  (check-true (expr? `⊤))
  (check-true (type-check (hash) `⊤ `prop))
)
|#
