#lang racket

(require racket/trace)

;; type ::=
;;   | `sexpr
;;   | `prop
;;   | `(=> ,type ,type)
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
;;   | `pair?
;;   | `empty?
;;   | `(= ,type)
;;   | `(∀ ,type)
;;   | `(∃ ,type)
;;   | `->
;;   | `and
;;   | `or
;;   | `(,synth ,expr ,expr ...)

(define (type? t)
  (match t
    [`sexpr #t]
    [`prop #t]
    [`(=> ,d ,c)
      (and (type? d) (type? c))]
    [_ #f]))

(define (type=? t u)
  (equal? t u))

(define (variable? x)
  (and
    (symbol? x)
    (not (set-member? (set 'λ 'cons 'quote '= '∀ '∃ '-> 'and 'or 'sexpr 'prop) x))))

(define (expr? e)
  (or (check? e) (synth? e)))

(define (check? e)
  (match e
    [`(λ ,x ,b)
      (and (variable? x) (expr? b))]
    [_ #f]))

(define (synth? e)
  (match e
    [(? variable?) #t]
    [`cons #t]
    [`(quote ,(? symbol?)) #t]
    [`() #t]
    [`symbol? #t]
    [`pair? #t]
    [`empty? #t]
    [`(= ,t) (type? t)]
    [`(∀ ,t) (type? t)]
    [`(∃ ,t) (type? t)]
    [`-> #t]
    [`and #t]
    [`or #t]
    [`(,f ,arg ,args ...)
      (and (synth? f) (expr? arg) (andmap expr? args))]
    [_ #f]))

(define/contract (subst e x a)
  (-> expr? variable? expr? expr?)
  (match e
    [`(λ ,y ,b)
      (let ([z (gensym)])
        `(λ ,z ,(subst (subst b y z) x a)))]
    [(? variable? y) #:when (symbol=? x y)
      a]
    [`cons e]
    [`(quote ,_) e]
    [`() e]
    [`symbol? e]
    [`pair? e]
    [`empty? e]
    [`(= ,_) e] [`(∀ ,_) e]
    [`(∃ ,_) e]
    [`-> e]
    [`and e]
    [`or e]
    [`(,f ,arg ,args ...)
     `(,(subst f x a) ,(subst arg x a) ,@(map (λ (arg) (subst arg x a)) args))]))

(define/contract (app f a)
  (-> expr? expr? expr?)
  (match f
    [`(λ ,x ,b)
      (subst b x a)]
    [f `(,f ,a)]))

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
    [(`(∀ ,t) `(∀ ,u)) (type=? t u)]
    [(`(∃ ,t) `(∃ ,u)) (type=? t u)]
    [(`-> `->) #t]
    [(`and `and) #t]
    [(`or `or) #t]
    [(`(,a-f ,a-arg ,a-args ...) `(,b-f ,b-arg ,b-args ...))
     (and (expr=? a-f b-f) (expr=? a-arg b-arg) (andmap expr=? a-args b-args))]))

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
    [(`(λ ,x ,b) `(=> ,d ,c))
     (type-check (dict-set env x d) b c)]
    [(`(λ ,_ ,_) _) #f]
    [(e t) (equal? t (type-synth env e))]))

(define/contract (type-synth env e)
  (-> type-env? expr? (or/c type? #f))

  (define (type-synth-app f-t arg args)
    (match* (f-t args)
      [(`(=> ,d ,c) `())
       (and (type-check env arg d) c)]
      [(`(=> ,d ,c) `(,next-arg ,args ...))
       (and (type-check env arg d) (type-synth-app c next-arg args))]
      [(_ _) #f]))

  (match e
    [(? variable? x) (dict-ref env x #f)]
    [`cons `(=> sexpr (=> sexpr sexpr))]
    [`(quote ,_) `sexpr]
    [`() `sexpr]
    [`symbol? `(=> sexpr prop)]
    [`pair? `(=> sexpr prop)]
    [`empty? `(=> sexpr prop)]
    [`(= ,t) `(=> ,t (=> ,t prop))]
    [`(∀ ,t) `(=> (=> ,t prop) prop)]
    [`(∃ ,t) `(=> (=> ,t prop) prop)]
    [`-> `(=> prop (=> prop prop))]
    [`and `(=> prop (=> prop prop))]
    [`or `(=> prop (=> prop prop))]
    [`(,f ,arg ,args ...) (type-synth-app (type-synth env f) arg args)]))

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

(define (proof? p)
  (match p
    [(? variable?) #t]
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
;; ,Γ |- ,p : (=> sexpr prop)
;; ,Γ | ,Θ |- ,empty : (,p `empty)
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
    [(`(->I ,x ,prf) `(-> ,A ,B))
     (proof-check type-env (dict-set proof-env x A) prf B)]
    [(`(->I ,_ ,_) _) #f]
    [(`(andI ,a ,b) `(and ,A ,B))
     (and (proof-check type-env proof-env a A) (proof-check type-env proof-env b B))]
    [(`(orI-L ,a) `(or ,A ,_))
     (proof-check type-env proof-env a A)]
    [(`(orI-R ,b) `(or ,_ ,B))
     (proof-check type-env proof-env b B)]
    [(`(orE ,or-p (,x ,l-p) (,y ,r-p)) prop)
     (match (proof-synth type-env proof-env or-p)
       [`(or ,A ,B)
         (and
           (proof-check type-env (dict-set proof-env x A) l-p prop)
           (proof-check type-env (dict-set proof-env y B) r-p prop))]
       [_ #f])]
    [(prf prop)
     (cond
       [(proof-synth type-env proof-env prf)
        =>
        (λ (synthed-prop) (expr=? prop synthed-prop))]
       [else #f])]))

(define/contract (proof-synth type-env proof-env prf)
  (-> type-env? proof-env? proof? (or/c expr? #f))
  (match prf
    [(? variable? x) (dict-ref proof-env x #f)]
    [`(ind-sexpr ,p ,empty-p ,sym-p ,pair-p)
      (and 
        (type-check type-env p `(=> sexpr prop))
        (proof-check type-env proof-env empty-p (app p `empty))
        (let ([x (gensym)])
          (proof-check type-env proof-env sym-p `((∀ sexpr) (λ ,x (-> (symbol? ,x) ,(app p x))))))
        (let ([x (gensym)] [y (gensym)])
          (proof-check type-env proof-env empty-p `((∀ sexpr) (λ ,x ((∀ sexpr) (λ ,y (-> (and ,(app p x) ,(app p y)) ,(app p `(cons ,x ,y)))))))))
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
        [`(-> ,A ,B)
          (and
            (proof-check type-env proof-env prec-p A)
            B)]
        [_ #f])]
    [`(andE-L ,p)
      (match (proof-synth type-env proof-env p)
        [`(and ,A ,_) A]
        [_ #f])]
    [`(andE-R ,p)
      (match (proof-synth type-env proof-env p)
        [`(and ,_ ,B) B]
        [_ #f])]
    [`(orE ,or-p (,x ,l-p) (,y ,r-p))
     (match (proof-synth type-env proof-env or-p)
       [`(or ,A ,B)
         (let
           ([l-prop (proof-synth type-env (dict-set proof-env x A) l-p)]
            [r-prop (proof-synth type-env (dict-set proof-env y B) r-p)])
           (and
             l-prop
             r-prop
             (expr=? l-prop r-prop)
             l-prop))]
       [_ #f])]
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
          (realizer/proof expr-env (dict-set proof-env y r) p-r)])]))

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

(module+ test
  (require rackunit)

  (define p0 `((∀ prop) (λ X (-> X X))))
  (check-true (expr? p0))
  (check-true (type-check (hash) p0 `prop))

  (define prf0 `(∀I X (->I X-prf X-prf)))
  (check-true (proof? prf0))
  (check-true (proof-check (hash) (hash) prf0 p0))

  (define p1 `(-> ((∃ sexpr) (λ x ((= sexpr) x x))) ((∃ sexpr) (λ x ((= sexpr) x x)))))
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
)
