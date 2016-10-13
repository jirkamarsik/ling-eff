;; We will extend the above idea of applying an operation to computations
;; that yield the operands to other operations. We introduce a macro that,
;; given an operator 'op, defines the extended versions '<<op, 'op>> and
;; '<<op>>.
(define-syntax (extend-operator-to-computations stx)
  (syntax-case stx ()
    [(_ op)
     (with-syntax ([opl (format-id stx "<<~a" #'op)]
                   [opr (format-id stx "~a>>" #'op)]
                   [oplr (format-id stx "<<~a>>" #'op)])
       #'(begin
           (define-metafunction BANANA+SPA
             opl : e e -> e
             [(opl e_x e_y)
              (>>= e_x (λ (x) (η ((op x) e_y))))])
           (define-metafunction BANANA+SPA
             opr : e e -> e
             [(opr e_x e_y)
              (>>= e_y (λ (y) (η ((op e_x) y))))])
           (define-metafunction BANANA+SPA
             oplr : e e -> e
             [(oplr e_x e_y)
              (>>= e_x (λ (x) (>>= e_y (λ (y) (η ((op x) y))))))])))]))

;; We have conjunction,
(extend-operator-to-computations ∧)
;; disjunction,
(extend-operator-to-computations ∨)
;; implication,
(extend-operator-to-computations ⇒)
;; equality (on individuals),
(extend-operator-to-computations =)
;; adding an individual to a context,
(extend-operator-to-computations ::-ι)
;; adding a proposition to a context,
(extend-operator-to-computations ::-o)
;; and concatenating contexts.
(extend-operator-to-computations ++)


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
