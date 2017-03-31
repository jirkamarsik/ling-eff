;; Dynamic Logic
;; =============
;;
;; This section introduces the logical operators that we will be using in
;; our grammar.  These are based on de Groote and Lebedeva's Type-Theoretic
;; Dynamic Logic.  Their lambda-banana definitions can be found in Section 8.1
;; of the dissertation.

(define-metafunction BANANA+SPA
  d∧ : e e -> e
  [(d∧ e_a e_b)
   (>>= e_a (λ (,(variable-not-in (term e_b) '_)) e_b))])

(define-metafunction BANANA+SPA
  d¬ : e -> e
  [(d¬ e_a)
   (>>= (dbox e_a) (λ (a) (! ASSERT (¬ a))))])

(define-metafunction BANANA+SPA
  d∃ : e -> e
  [(d∃ e_pred)
   ,(term-let ([x_f (variable-not-in (term e_pred) 'x)])
              (term (FRESH ★ (λ (x_f) (e_pred x_f)))))])

(define-metafunction BANANA+SPA
  d⇒ : e e -> e
  [(d⇒ e_a e_b)
   (d¬ (d∧ e_a (d¬ e_b)))])

(define-metafunction BANANA+SPA
  d∨ : e e -> e
  [(d∨ e_a e_b)
   (d¬ (d∧ (d¬ e_a) (d¬ e_b)))])

(define-metafunction BANANA+SPA
  d∀ : e -> e
  [(d∀ e_pred)
   ,(term-let ([x_f (variable-not-in (term e_pred) 'x)])
              (term (d¬ (d∃ (λ (x_f) (d¬ (e_pred x_f)))))))])
