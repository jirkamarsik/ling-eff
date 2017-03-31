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
              ,(term-let ([x_f (variable-not-in (term e_y) 'x)])
                (term (>>= e_x (λ (x_f) (η ((op x_f) e_y))))))])
           (define-metafunction BANANA+SPA
             opr : e e -> e
             [(opr e_x e_y)
              ,(term-let ([x_f (variable-not-in (term e_x) 'y)])
                (term (>>= e_y (λ (x_f) (η ((op e_x) x_f))))))])
           (define-metafunction BANANA+SPA
             oplr : e e -> e
             [(oplr e_x e_y)
              ,(term-let ([x_f1 (variable-not-in (term e_y) 'x)]
                          [x_f2 (variable-not-in (term x_f1) 'y)])
                (term (>>= e_x (λ (x_f1) (>>= e_y (λ (x_f2) (η ((op x_f1) x_f2))))))))])))]))


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


