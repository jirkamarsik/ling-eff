;; The next three definitions concern the expression of Boolean values
;; using sums (Subsection 1.5.4 in the dissertation). We define constants
;; for true...
(define-checked-term true
  (inl ★))
;; and false.
(define-checked-term false
  (inr ★))
;; Finally, we define if-then-else expressions using case analysis.
(define-metafunction BANANA+SPA
  ifte : e e e -> e
  [(ifte e_cond e_then e_else)
   (case e_cond (λ (,(variable-not-in (term e_then) '_)) e_then)
         (λ (,(variable-not-in (term e_else) '_)) e_else))])
