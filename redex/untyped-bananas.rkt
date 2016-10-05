#lang racket
(require redex)

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
      BANANA+SP
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
           (η E (λ (x) e))
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

  [(proposition-in (John e_x) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in (man e_x) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in (Mary e_x) e_c)
   -----------------------------
   (has-gender e_x feminine e_c)]

  [(proposition-in (woman e_x) e_c)
   -----------------------------
   (has-gender e_x feminine e_c)]

  [(proposition-in (Porsche e_x) e_c)
   ----------------------------
   (has-gender e_x neutral e_c)]

  [(proposition-in (Mercedes e_x) e_c)
   ----------------------------
   (has-gender e_x neutral e_c)]

  [(proposition-in ((best-friend e_x) e_y) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in ((best-friend e_x) e_y) e_c)
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
      (--> ((++ ((::-i e_h) e_t)) e_2)
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






(define-metafunction BANANA+SPAC
  >>= : e e -> e
  [(>>= e_m e_k)
   (with (η e_k) handle e_m)])

(define-metafunction BANANA+SPAC
  ! : e e -> e
  [(! OP e)
   (OP e (λ (x) (η x)))])

(define-metafunction BANANA+SPAC
  with-η : (OP e) ... handle e -> e
  [(with-η (OP e_h) ... handle e_arg)
   (with (OP e_h) ... (η (λ (x) (η x))) handle e_arg)])

(define-metafunction BANANA+SPAC
  ∘ : e e -> e
  [(∘ e_1 e_2)
   (λ (x) (e_1 (e_2 x)))])



(define drs-handler
  (term (λ (A)
          (with
            (GET (λ (_) (λ (k)
                   (η (λ (e) (GET ★ (λ (e_) (>>= (k ((++ e) e_))
                                                 (λ (f) (f e))))))))))
            (FRESH (λ (_) (λ (k)
                     (η (λ (e) (>>= (C (λ (x) (>>= (k x)
                                                   (λ (f) (f e)))))
                                    (λ (pred) (η (∃ pred)))))))))
            (PUSH (λ (x) (λ (k)
                    (η (λ (e) (>>= (k ★)
                                   (λ (f) (f ((::-ι x) e)))))))))
            (ASSERT (λ (p) (λ (k)
                      (η (λ (e) (>>= (k ★)
                                     (λ (f) (>>= (f ((::-o p) e))
                                                 (λ (q) (η ((∧ p) q)))))))))))
            (η (λ (_) (η (λ (e) (η ⊤)))))
           handle A))))

(define box
  (term (λ (A)
          (>>= (,drs-handler A)
               (λ (f) (f nil))))))

(define SI
  (term (λ (A)
          (with-η
            (SCOPE (λ (c) (λ (k) (c k))))
           handle A))))