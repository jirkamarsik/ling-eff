;; We can now define the reduction relation of our calculus. This follows
;; closely the definitions given in Chapter 1 of the dissertation.
(define reduce
  (compatible-closure 
    (reduction-relation BANANA+SPA #:domain e
      (--> ((λ (x) e_1) e_2)
           (subst e_1 x e_2)
           "β")
      (--> (λ (x) (e x))
           e
           (side-condition (not (term (free-in x e))))
           "η")
      (--> (with (OP_i e_i) ... (η e_p) handle (η e_v))
           (e_p e_v)
           "handle-η")
      (--> (with (OP_1 e_1) ... (OP_2 e_2) (OP_3 e_3) ... (η e_p)
            handle (OP_2 e_arg (λ (x) e_m)))
           ((e_2 e_arg) (λ (x_f) (with (OP_1 e_1) ...
                                       (OP_2 e_2)
                                       (OP_3 e_3) ...
                                       (η e_p)
                                  handle (subst e_m x x_f))))
           (side-condition (term (no-match OP_2 (OP_1 ...))))
           (fresh x_f)
           "handle-OP")
      (--> (with (OP_i e_i) ... (η e_p) handle (OP e_arg (λ (x) e_m)))
           (OP e_arg (λ (x_f) (with (OP_i e_i) ...
                                    (η e_p)
                               handle (subst e_m x x_f))))
           (side-condition (term (no-match OP (OP_i ...))))
           (fresh x_f)
           "handle-missing-OP")
      (--> (♭ (η e))
           e
           "♭")
      (--> (C (λ (x) (η e)))
           (η (λ (x) e))
           "𝓒-η")
      (--> (C (λ (x) (OP e_a (λ (x_k) e_k))))
           (OP e_a (λ (x_k) (C (λ (x) e_k))))
           (side-condition (not (term (free-in x e_a))))
           "𝓒-OP")
      (--> (π1 (pair e_1 e_2))
           e_1
           "β.×1")
      (--> (π2 (pair e_1 e_2))
           e_2
           "β.×2")
      (--> (case (inl e) e_l e_r)
           (e_l e)
           "β.+1")
      (--> (case (inr e) e_l e_r)
           (e_r e)
           "β.+2")) BANANA+SPA e))
