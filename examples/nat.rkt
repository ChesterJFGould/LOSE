#lang lose

(define nat?-consequence (=> (=> sexpr prop) (=> sexpr prop))
  (λ nat? (λ n (or ((= sexpr) n 'z) (∃ [m : sexpr] (and (nat? m) ((= sexpr) n (cons 's m))))))))

(define nat?-exi prop
  (∃ [nat? : (=> sexpr prop)]
    (and
      (∀ [n : sexpr] (-> (nat? n) (nat?-consequence nat? n))
      (∀ [n : sexpr] (-> (nat?-consequence nat? n) (nat? n)))))))

