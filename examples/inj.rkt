#lang lose

(defthm sexpr-refl (∀ [s : sexpr] (((= sexpr) s) s))
  (ind-sexpr
    (λ s (((= sexpr) s) s))
    =I
    (∀I s (->I x =I))
    (∀I a (∀I b (->I x =I)))))

(define not (=> prop prop)
  (λ p (-> p ⊥)))

#;
(define =consequence-prop prop
  (∃ [=conse : (=> sexpr (=> sexpr prop))]
    (and
      (=conse empty empty)
      (∀ [s : sexpr] (-> (symbol? s) (not (=conse empty s))))
      (∀ [a : sexpr] [b : sexpr] (not (=conse empty (cons a b))))
      (∀ [s : sexpr] (-> (symbol? s) (=conse s s)))
      (∀ [s : sexpr] (-> (symbol? s) (not (=conse s empty))))
      (∀ [s : sexpr] (-> (symbol? s) (not (=conse s empty))))
      _)))

(defthm cons-inj
  (∀ [a : sexpr] [b : sexpr] [c : sexpr] [d : sexpr]
    (-> ((= sexpr) (cons a b) (cons c d))
      (and ((= sexpr) a c) ((= sexpr) b d))))
  (∀I a (∀I b (∀I c (∀I d
    (->I x (andI _ _)))))))
