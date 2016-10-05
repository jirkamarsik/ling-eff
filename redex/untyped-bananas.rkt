#lang racket
(require redex)
(require (for-syntax racket/syntax))

(define-language BANANA
  (e ::= x
         c
         (e e)
         (λ (x) e)
         (η e)
         (OP e (λ (x) e))
         (with (OP e) ... (η e) handle e)
         (♭ e)
         (C e))
  (x ::= variable-not-otherwise-mentioned)
  (c ::= variable-not-otherwise-mentioned)
  (OP ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x) e #:refers-to x))

(define-extended-language BANANA+SP
  BANANA
  (e ::= ....
         ★
         (π1 e)
         (π2 e)
         (pair e e)
         (inl e)
         (inr e)
         (case e (inl x → e)
                 (inr x → e))
         (absurd e))
  #:binding-forms
  (case e (inl x → e_l #:refers-to x)
          (inr y → e_r #:refers-to y)))

(define-extended-language BANANA+SPA
  BANANA+SP
  (e ::= ....
         (e || e)))



(define-metafunction BANANA+SPA
  no-match : any (any ...) -> #t or #f
  [(no-match any_1 (any_1 any_more ...))
   #f]
  [(no-match any_1 (any_2 any_more ...))
   (no-match any_1 (any_more ...))]
  [(no-match any_1 ())
   #t])

(define-metafunction BANANA+SPA
  free-in : x e -> #t or #f
  [(free-in x (e_f e_a))
   ,(or (term (free-in x e_f)) (term (free-in x e_a)))]
  [(free-in x (λ (x) e))
   #f]
  [(free-in x (λ (x_different) e))
   (free-in x e)]
  [(free-in x x)
   #t]
  [(free-in x x_different)
   #f]
  [(free-in x c)
   #f]
  [(free-in x (η e))
   (free-in x e)]
  [(free-in x (OP e_arg e_k))
   ,(or (term (free-in x e_arg)) (term (free-in x e_k)))]
  [(free-in x (with (OP_i e_i) ... (η e_p) handle e))
   ,(or (ormap identity (term ((free-in x e_i) ...)))
        (term (free-in x e_p))
        (term (free-in x e)))]
  [(free-in x (C e))
   (free-in x e)]
  [(free-in x ★)
   #f]
  [(free-in x (π1 e))
   (free-in x e)]
  [(free-in x (π2 e))
   (free-in x e)]
  [(free-in x (pair e_1 e_2))
   ,(or (term (free-in x e_1)) (term (free-in x e_2)))]
  [(free-in x (inl e))
   (free-in x e)]
  [(free-in x (inr e))
   (free-in x e)]
  [(free-in x (case e (inl x_l → e_l)
                      (inr x_r → e_r)))
   ,(or (term (free-in x e))
        (term (free-in x (λ (x_l 1) e_l)))
        (term (free-in x (λ (x_r 1) e_r))))]
  [(free-in x (absurd e))
   (free-in x e)]
  [(free-in x (e_1 || e_2))
   ,(or (term (free-in x e_1)) (term (free-in x e_2)))])



(define eval
  (compatible-closure 
    (reduction-relation
      BANANA+SPA
      #:domain e
      (--> ((λ (x) e_1) e_2)
           (substitute e_1 x e_2)
           "β")
      (--> (λ (x) (e x))
           e
           (side-condition (not (term (free-in x e))))
           "η")
      (--> (with (OP_i e_i) ... (η e_p) handle (η e_v))
           (e_p e_v)
           "handle-η")
      (--> (with (OP_1 e_1) ... (OP_2 e_2) (OP_3 e_3) ... (η e_p) handle (OP_2 e_arg (λ (x) e_m)))
           ((e_2 e_arg) (λ (x) (with (OP_1 e_1) ... (OP_2 e_2) (OP_3 e_3) ... (η e_p) handle e_m)))
           (side-condition (term (no-match OP_2 (OP_1 ...))))
           "handle-OP")
      (--> (with (OP_i e_i) ... (η e_p) handle (OP e_arg (λ (x) e_m)))
           (OP e_arg (λ (x) (with (OP_i e_i) ... (η e_p) handle e_m)))
           (side-condition (term (no-match OP (OP_i ...))))
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
      (--> (case (inl e) (inl x → e_l)
                         (inr y → e_r))
           (substitute e x e_l)
           "β.+1")
      (--> (case (inr e) (inl x → e_l)
                         (inr y → e_r))
           (substitute e y e_r)
           "β.+2")
      (--> (e_1 || e_2)
           e_1
           ";1")
            (--> (e_1 || e_2)
           e_2
           ";2"))
    BANANA+SPA
    e))






(define-extended-language BANANA+SPAC
  BANANA+SPA
  (gender ::= masculine
              feminine
              neutral))

(define-judgment-form
  BANANA+SPAC
  #:mode (individual-in O I)
  #:contract (individual-in e e)

  [----------------------------------------------
   (individual-in e_ind ((::-ι e_ind) e_context))]
  
  [(individual-in e_ind e_context)
   ------------------------------------------------
   (individual-in e_ind ((::-ι e_other) e_context))]

  [(individual-in e_ind e_context)
   ------------------------------------------------
   (individual-in e_ind ((::-o e_other) e_context))])

(define-judgment-form
  BANANA+SPAC
  #:mode (proposition-in O I)
  #:contract (proposition-in e e)

  [-------------------------------------------------
   (proposition-in e_prop ((::-o e_prop) e_context))]
  
  [(proposition-in e_prop e_context)
   --------------------------------------------------
   (proposition-in e_prop ((::-ι e_other) e_context))]

  [(proposition-in e_prop e_context)
   --------------------------------------------------
   (proposition-in e_prop ((::-o e_other) e_context))])

(define-judgment-form
  BANANA+SPAC
  #:mode (has-gender I I I)
  #:contract (has-gender e gender e)

  [(proposition-in (John* e_x) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in (man* e_x) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in (Mary* e_x) e_c)
   -----------------------------
   (has-gender e_x feminine e_c)]

  [(proposition-in (woman* e_x) e_c)
   -----------------------------
   (has-gender e_x feminine e_c)]

  [(proposition-in (Porsche* e_x) e_c)
   ----------------------------
   (has-gender e_x neutral e_c)]

  [(proposition-in (Mercedes* e_x) e_c)
   ----------------------------
   (has-gender e_x neutral e_c)]

  [(proposition-in ((best-friend* e_x) e_y) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in ((best-friend* e_x) e_y) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)])

(define-judgment-form
  BANANA+SPAC
  #:mode (sel I I O)
  #:contract (sel gender e e)

  [(individual-in e_referent e_context)
   (has-gender e_referent gender e_context)
   ---------------------------------
   (sel gender e_context e_referent)])

(define-judgment-form
  BANANA+SPAC
  #:mode (all-conds-in I I)
  #:contract (all-conds-in e e)

  [(all-conds-in e_c1 e_context)
   (all-conds-in e_c2 e_context)
   ----------------------------------------
   (all-conds-in ((∧ e_c1) e_c2) e_context)]

  [(proposition-in e_condition e_context)
   ------------------------------------
   (all-conds-in e_condition e_context)])

(define-judgment-form
  BANANA+SPAC
  #:mode (sel-prop I I O)
  #:contract (sel-prop e e e)

  [(individual-in e_referent e_context)
   (all-conds-in (substitute e_condition x e_referent) e_context)
   -----------------------------------------------------
   (sel-prop (λ (x ι) e_condition) e_context e_referent)]

  [(individual-in e_referent e_context)
   (all-conds-in (e_property e_referent) e_context)
   -----------------------------------------------------
   (sel-prop e_property e_context e_referent)])

(define eval-more
  (compatible-closure
    (extend-reduction-relation eval
      BANANA+SPAC
      (--> ((++ nil) e)
           e
           "++ nil")
      (--> ((++ ((::-ι e_h) e_t)) e_2)
           ((::-ι e_h) ((++ e_t) e_2))
           "++ ::-ι")
      (--> ((++ ((::-o e_h) e_t)) e_2)
           ((::-o e_h) ((++ e_t) e_2))
           "++ ::-o")
      (--> (sel-he e_context)
           e_referent
           (judgment-holds (sel masculine e_context e_referent))
           "sel-he")
      (--> (sel-she e_context)
           e_referent
           (judgment-holds (sel feminine e_context e_referent))
           "sel-she")
      (--> (sel-it e_context)
           e_referent
           (judgment-holds (sel neutral e_context e_referent))
           "sel-it")
      (--> ((selP e_property) e_context)
           e_referent
           (judgment-holds (sel-prop e_property e_context e_referent))
           "selP"))
    BANANA+SPAC
    e))



(define (normalize t)
  (let [(steps (apply-reduction-relation eval-more t))]
    (if (null? steps)
      t
      (normalize (car steps)))))

(define-metafunction BANANA+SPA
  [(to-binary variable)
   variable]
  [(to-binary (λ (x) any))
   (λ (x) (to-binary any))]
  [(to-binary (λ (x_0 x ...) e))
   (λ (x_0) (to-binary (λ (x ...) e)))]
  [(to-binary (any_0 any_1))
   ((to-binary any_0) (to-binary any_1))]
  [(to-binary (any_0 any_1 any ...))
   (to-binary ((any_0 any_1) any ...))])






(define-metafunction BANANA+SPA
  >>= : e e -> e
  [(>>= e_m e_k)
   (with (η e_k) handle e_m)])

(define-metafunction BANANA+SPA
  [(! OP)
   (λ (x) (OP x (λ (y) (η y))))]
  [(! OP e)
   (OP e (λ (x) (η x)))])

(define-metafunction BANANA+SPA
  with-η : (OP e) ... handle e -> e
  [(with-η (OP e_h) ... handle e_arg)
   (with (OP e_h) ... (η (λ (x) (η x))) handle e_arg)])

(define-metafunction BANANA+SPA
  handler : (OP e) ... (η e) -> e
  [(handler (OP e_h) ... (η e_p))
   (λ (x) (with (OP e_h) ... (η e_p) handle x))])

(define-metafunction BANANA+SPA
  handler-η : (OP e) ... -> e
  [(handler-η (OP e_h) ...)
   (λ (x) (with-η (OP e_h) ... handle x))])

(define-term true
  (inl ★))

(define-term false
  (inr ★))

(define-metafunction BANANA+SPA
  ifte : e e e -> e
  [(ifte e_cond e_then e_else)
   (case e_cond (inl x_l → e_then)
                (inr x_r → e_else))])

(define-metafunction BANANA+SPA
  choose : e e -> e
  [(choose e_1 e_2)
   (AMB ★ (λ (b) (ifte b e_1 e_2)))])

(define-metafunction BANANA+SPA
  ∘ : e ... -> e
  [(∘)
   (λ (x) x)]
  [(∘ e)
   e]
  [(∘ e_f e_g)
   (λ (x) (f (g x)))]
  [(∘ e_1 e_2 e_more ...)
   (∘ (∘ e_1 e_2) e_more ...)])

(define-syntax (extend-operator-to-computations stx)
  (syntax-case stx ()
    [(_ op mf)
     (with-syntax ([opl (format-id stx "<<~a" #'op)]
                   [opr (format-id stx "~a>>" #'op)]
                   [oplr (format-id stx "<<~a>>" #'op)])
       #'(begin
           (define-metafunction BANANA+SPA
             opl : e e -> e
             [(opl e_x e_y)
             (>>= e_x (λ (x) (η (mf x e_y))))])
           (define-metafunction BANANA+SPA
             opr : e e -> e
             [(opr e_x e_y)
             (>>= e_y (λ (y) (η (mf e_x y))))])
           (define-metafunction BANANA+SPA
             oplr : e e -> e
             [(oplr e_x e_y)
             (>>= e_x (λ (x) (>>= e_y (λ (y) (η (mf x y))))))])))]))

(define-metafunction BANANA+SPA
  ap : e e -> e
  [(ap e_f e_x)
   (e_f e_x)])

(define-syntax-rule (define-binary-operator mf op)
  (define-metafunction BANANA+SPA
    mf : e e -> e
    [(mf e_1 e_2)
     ((op e_1) e_2)]))

(define-binary-operator land ∧)
(define-binary-operator lor ∨)
(define-binary-operator limp ⇒)
(define-binary-operator eq =)
(define-binary-operator consi-ctx ::-ι)
(define-binary-operator conso-ctx ::-o)
(define-binary-operator cat-ctx ++)

(extend-operator-to-computations · ap)
(extend-operator-to-computations ∧ land)
(extend-operator-to-computations ∨ lor)
(extend-operator-to-computations ⇒ limp)
(extend-operator-to-computations = eq)
(extend-operator-to-computations ::-ι consi-ctx)
(extend-operator-to-computations ::-o conso-ctx)
(extend-operator-to-computations ++ cat-ctx)

(define-metafunction BANANA+SPA
  <<<· : e e -> e
  [(<<<· e_f e_x)
   (>>= e_f (λ (f) (f e_x)))])

(define-metafunction BANANA+SPA
  ∃>> : e -> e
  [(∃>> e_pred)
   (·>> ∃ (C e_pred))])






(define-term box
  (λ (A)
    (<<<· ((handler
      (GET (λ (_) (λ (k)
             (η (λ (e) (GET ★ (λ (e_) (<<<· (k (cat-ctx e e_)) e))))))))
      (FRESH (λ (_) (λ (k)
               (η (λ (e) (∃>> (λ (x) (<<<· (k x) e))))))))
      (PUSH (λ (x) (λ (k)
              (η (λ (e) (<<<· (k ★) (consi-ctx x e)))))))
      (ASSERT (λ (p) (λ (k)
                (η (λ (e) (∧>> p (<<<· (k ★) (conso-ctx p e))))))))
      (η (λ (_) (η (λ (e) (η ⊤)))))) A) nil)))

(define-term dbox
  (∘ box maybeAccommodate useFind))

(define-metafunction BANANA+SPA
  INTRODUCE : e e -> e
  [(INTRODUCE e_u e_k)
   (FRESH e_u (λ (x) (PUSH x (λ (x_) (e_k x)))))])

(define-term empty
  (handler-η (GET (λ (_) (λ (k) (k nil))))))

(define-term accommodate
  (handler-η (PRESUPPOSE (λ (P) (λ (k)
               (INTRODUCE ★ (λ (x) (>>= (P x) (λ (_) (k x))))))))))

(define-term maybeAccommodate
  (handler-η (PRESUPPOSE (λ (P) (λ (k)
               (choose (PRESUPPOSE P k) (INTRODUCE ★ (λ (x) (>>= (P x) (λ (_) (k x)))))))))))

(define-term useFind
  (handler-η (PRESUPPOSE (λ (P) (λ (k) (>>= (find P) k))))))

(define-term find
  (λ (P) (GET ★ (λ (e) (case ((selP (λ (x) (♭ (top (P x))))) e)
                         (inl x → (η x))
                         (inr _ → (! PRESUPPOSE P)))))))

(define-term search
  (handler-η (AMB (λ (_) (λ (k) ((k true) || (k false)))))))

(define-term SI
  (handler-η (SCOPE (λ (c) (λ (k) (c k))))))



(define-term top
  (∘ search empty box accommodate useFind))



(define-metafunction BANANA+SPA
  d∧ : e e -> e
  [(d∧ e_a e_b)
   (>>= e_a (λ (x_) e_b))])

(define-metafunction BANANA+SPA
  d¬ : e -> e
  [(d¬ e_a)
   (>>= (dbox e_a) (λ (a) (! ASSERT (¬ a))))])

(define-metafunction BANANA+SPA
  d∃ : e -> e
  [(d∃ e_pred)
   (INTRODUCE ★ e_pred)])

(define-metafunction BANANA+SPA
  d→ : e e -> e
  [(d→ e_a e_b)
   (d¬ (d∧ e_a (d¬ e_b)))])

(define-metafunction BANANA+SPA
  d∨ : e e -> e
  [(d∨ e_a e_b)
   (d¬ (d∧ (d¬ e_a) (d¬ e_b)))])

(define-metafunction BANANA+SPA
  d∀ : e -> e
  [(d∀ e_pred)
   (d¬ (d∃ (λ (x) (d¬ (e_pred x)))))])



(define-term she
  (GET ★ (λ (e)
  (η (sel-she e)))))

(define-term he
  (GET ★ (λ (e)
  (η (sel-he e)))))

(define-term it
  (GET ★ (λ (e)
  (η (sel-it e)))))

(define-syntax-rule (define-common-noun abstract object)
  (define-term abstract
    (λ (x) (! ASSERT (object x)))))

(define-common-noun man man*)
(define-common-noun woman woman*)
(define-common-noun Porsche Porsche*)
(define-common-noun Mercedes Mercedes*)

(define-term indef
  (λ (n) (INTRODUCE ★ (λ (x)
         (>>= (n x) (λ (_)
         (η x)))))))

(define-syntax-rule (define-proper-noun abstract object)
  (define-term abstract
    (INTRODUCE ★ (λ (x)
    (ASSERT (object x) (λ (_)
    (η x)))))))

(define-proper-noun John John*)
(define-proper-noun Mary Mary*)

(define-syntax-rule (define-transitive-verb abstract object)
  (define-term abstract
    (λ (O) (λ (S)
      (>>= (<<·>> (·>> object S) O)
           (! ASSERT))))))

(define-transitive-verb loves love*)
(define-transitive-verb owns own*)
(define-transitive-verb fascinates fascinate*)

(define-term not-the-case
  (λ (A) (d¬ A)))

(define-term and-sent
  (λ (A) (λ (B) (d∧ A B))))

(define-term if-then
  (λ (A) (λ (B) (d→ A B))))

(define-term either-or
  (λ (A) (λ (B) (d∨ A B))))

(define-term dot
  (λ (D) (λ (S) (>>= D (λ (_) S)))))

(define-term nil-disc
  (η ★))

(define-term the
  (λ (N) (>>= (packageProperty (λ (x) (PUSH x (λ (_) (N x))))) (λ (N_)
         (! PRESUPPOSE N_)))))

(define-term poss
  (λ (X) (λ (N) (>>= X (λ (x)
                (>>= (packageProperty (λ (y) (PUSH y (λ (_) (ASSERT ((own* x) y) (λ (_) (N y)))))))
                (! PRESUPPOSE N_)))))))

(define-syntax-rule (define-relational-noun abstract object)
  (define-term abstract
    (λ (X) (>>= X (λ (x)
           (! PRESUPPOSE (λ (y) (! ASSERT ((object y) x)))))))))

(define-relational-noun children-of children*)
(define-relational-noun best-friend best-friend*)

(define-term inTheContext
  (λ (e) (handler-η (GET (λ (_) (λ (k) (GET ★ (λ (e_) (k (cat-ctx e e_))))))))))

(define-term splitDRT
  (handler (GET (λ (x) (λ (k) (·>> (λ (c) (GET x c)) (C k)))))
           (FRESH (λ (x) (λ (k) (·>> (λ (c) (FRESH x c)) (C k)))))
           (PUSH (λ (x) (λ (k) (·>> (λ (c) (PUSH x c)) (C k)))))
           (ASSERT (λ (x) (λ (k) (·>> (λ (c) (ASSERT x c)) (C k)))))
           (η (λ (x) (η (η x))))))

(define-term packageProperty
  (λ (P) (GET ★ (λ (e)
         (C (λ (x) (splitDRT ((inTheContext e) (maybeAccommodate (SI (P x)))))))))))