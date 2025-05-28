#lang lose

(defthm sexpr-refl (∀ [s : sexpr] (((= sexpr) s) s))
  (ind-sexpr
    (λ s (((= sexpr) s) s))
    =I
    (∀I s (->I x =I))
    (∀I a (∀I b (->I x =I)))))

(defthm cons-inj
  (∀ [a : sexpr] [b : sexpr] [c : sexpr] [d : sexpr]
    (-> ((= sexpr) (cons a b) (cons c d))
      (and ((= sexpr) a c) ((= sexpr) b d))))
  (∀I a (∀I b (∀I c (∀I d
    (->I x (andI _ _)))))))
