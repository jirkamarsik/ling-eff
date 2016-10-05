#lang racket
(require redex)

(define-language BANANA
  (e ::= x
         c
         (e e)
         (λ (x τ) e)
         (η E e)
         (OP e (λ (x τ) e))
         (with (OP e) ... (η e) handle e)
         (♭ e)
         (C e))
  (τ ::= (τ → τ)
         ν
         (F E τ))
  (x ::= variable-not-otherwise-mentioned)
  (c ::= variable-not-otherwise-mentioned)
  (ν ::= variable-not-otherwise-mentioned)
  (OP ::= variable-not-otherwise-mentioned)
  (Γ ::= · (x : τ Γ))
  (Σ ::= · (c : τ Σ))
  (E ::= · (OP : (τ ↦ τ) E))
  (context ::= Γ Σ E)
  (key ::= x c OP)
  #:binding-forms
  (λ (x τ) e #:refers-to x))

(define-extended-language BANANA+SP
  BANANA
  (e ::= ....
         ★
         (π1 e)
         (π2 e)
         (pair e e)
         (inl τ e)
         (inr τ e)
         (case e (inl x → e)
                 (inr x → e))
         (absurd τ e))
  (τ ::= ....
         1
         (τ × τ)
         0
         (τ + τ))
  #:binding-forms
  (case e (inl x → e_l #:refers-to x)
          (inr y → e_r #:refers-to y)))

(define-extended-language BANANA+SPA
  BANANA+SP
  (e ::= ....
         (e || e)))



(define-metafunction BANANA+SPA
  different : any any -> #t or #f
  [(different any_1 any_1) #f]
  [(different any_1 any_2) #t])

(define-metafunction BANANA+SPA
  all-match : any (any ...) -> #t or #f
  [(all-match any_1 (any_1 any_more ...))
   (all-match any_1 (any_more ...))]
  [(all-match any_1 (any_2 any_more ...))
   #f]
  [(all-match any_1 ())
   #t])

(define-metafunction BANANA+SPA
  no-match : any (any ...) -> #t or #f
  [(no-match any_1 (any_1 any_more ...))
   #f]
  [(no-match any_1 (any_2 any_more ...))
   (no-match any_1 (any_more ...))]
  [(no-match any_1 ())
   #t])

(define-metafunction BANANA+SPA
  add/replace : key any context -> context
  [(add/replace key_1 any_1 ·)
   (key_1 : any_1 ·)]
  [(add/replace key_1 any_1 (key_1 : any_2 context_2))
   (key_1 : any_1 context_2)]
  [(add/replace key_1 any_1 (key_2 : any_2 context_2))
   (key_2 : any_2 (add/replace key_1 any_1 context_2))])

(define-metafunction BANANA+SPA
  merge-ctxs : context context -> context
  [(merge-ctxs · context_2)
   context_2]
  [(merge-ctxs (key_1 : any_1 context_1) context_2)
   (add/replace key_1 any_1 (merge-ctxs context_1 context_2))])

(define-metafunction BANANA+SPA
  ctx-from-ellipsis : ((key any) ...) -> context
  [(ctx-from-ellipsis ())
   ·]
  [(ctx-from-ellipsis ((key_1 any_1) (key_more any_more) ...))
   (key_1 : any_1 (ctx-from-ellipsis ((key_more any_more) ...)))])

(define-metafunction BANANA+SPA
  free-in : x e -> #t or #f
  [(free-in x (e_f e_a))
   ,(or (term (free-in x e_f)) (term (free-in x e_a)))]
  [(free-in x (λ (x τ) e))
   #f]
  [(free-in x (λ (x_different τ) e))
   (free-in x e)]
  [(free-in x x)
   #t]
  [(free-in x x_different)
   #f]
  [(free-in x c)
   #f]
  [(free-in x (η E e))
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
  [(free-in x (inl τ e))
   (free-in x e)]
  [(free-in x (inr τ e))
   (free-in x e)]
  [(free-in x (case e (inl x_l → e_l)
                      (inr x_r → e_r)))
   ,(or (term (free-in x e))
        (term (free-in x (λ (x_l 1) e_l)))
        (term (free-in x (λ (x_r 1) e_r))))]
  [(free-in x (absurd τ e))
   (free-in x e)]
  [(free-in x (e_1 || e_2))
   ,(or (term (free-in x e_1)) (term (free-in x e_2)))])



(define-judgment-form
  BANANA+SPA
  #:mode (∈ I O I)
  #:contract (∈ key any context)
  
  [---------------------------------------
   (∈ key_1 any_1 (key_1 : any_1 context))]
  
  [(∈ key_1 any_1 context)
   (side-condition (different key_1 key_2))
   ---------------------------------------
   (∈ key_1 any_1 (key_2 : any_2 context))])

(define-judgment-form
  BANANA+SPA
  #:mode (context-included I I)
  #:contract (context-included context context)

  [------------------------------
   (context-included · context_2)]

  [(∈ key_1 any_1 context_2)
   (context-included context_1 context_2)
   ------------------------------------------------------
   (context-included (key_1 : any_1 context_1) context_2)])



(define-judgment-form
  BANANA+SPA
  #:mode (⊢ I I I O)
  #:contract (⊢ Γ Σ e τ)
  
  [(⊢ Γ Σ e_1 (τ_2 → τ_3))
   (⊢ Γ Σ e_2 τ_2)
   --------------------- "app"
   (⊢ Γ Σ (e_1 e_2) τ_3)]
  
  [(⊢ (x : τ_1 Γ) Σ e τ_2)
   --------------------------------- "abs"
   (⊢ Γ Σ (λ (x τ_1) e) (τ_1 → τ_2))]
  
  [(∈ x τ Γ)
   ----------- "var"
   (⊢ Γ Σ x τ)]
  
  [(∈ c τ Σ)
   ----------- "const"
   (⊢ Γ Σ c τ)]
  
  [(⊢ Γ Σ e τ)
   ----------------------- "η"
   (⊢ Γ Σ (η E e) (F E τ))]
  
  [(⊢ Γ Σ e_arg τ_1)
   (⊢ Γ Σ e_k (τ_2 → (F E τ_3)))
   (∈ OP (τ_1 ↦ τ_2) E)
   -------------------------------- "OP"
   (⊢ Γ Σ (OP e_arg e_k) (F E τ_3))]
  
  [(⊢ Γ Σ e_h (τ_arg → ((τ_res → (F E_out_h τ_out_h)) → (F E_out_h τ_out_h)))) ...
   (⊢ Γ Σ e_p (τ_in → (F E_out τ_out)))
   (⊢ Γ Σ e (F E_in τ_in))
   (where E (ctx-from-ellipsis ((OP (τ_arg ↦ τ_res)) ...)))
   (context-included E_in (merge-ctxs E_out E))
   (side-condition (all-match τ_out (τ_out_h ...)))
   (side-condition (all-match E_out (E_out_h ...)))
   ------------------------------------------------------------ "handle"
   (⊢ Γ Σ (with (OP e_h) ... (η e_p) handle e) (F E_out τ_out))]
  
  [(⊢ Γ Σ e (F E τ))
   --------------- "♭"
   (⊢ Γ Σ (♭ e) τ)]
  
  [(⊢ Γ Σ e (τ_1 → (F E τ_2)))
   ------------------------------- "𝓒"
   (⊢ Γ Σ (C e) (F E (τ_1 → τ_2)))]

  [----------- "★"
   (⊢ Γ Σ ★ 1)]

  [(⊢ Γ Σ e (τ_1 × τ_2))
   ------------------ "π1"
   (⊢ Γ Σ (π1 e) τ_1)]

  [(⊢ Γ Σ e (τ_1 × τ_2))
   ------------------ "π2"
   (⊢ Γ Σ (π2 e) τ_2)]

  [(⊢ Γ Σ e_1 τ_1)
   (⊢ Γ Σ e_2 τ_2)
   ---------------------------------- "pair"
   (⊢ Γ Σ (pair e_1 e_2) (τ_1 × τ_2))]

  [(⊢ Γ Σ e_l τ_l)
   --------------------------------- "inl"
   (⊢ Γ Σ (inl τ_r e_l) (τ_l + τ_r))]
  
  [(⊢ Γ Σ e_r τ_r)
   --------------------------------- "inr"
   (⊢ Γ Σ (inr τ_l e_r) (τ_l + τ_r))]

  [(⊢ Γ Σ e (τ_l + τ_r))
   (⊢ (x_l : τ_l Γ) Σ e_l τ)
   (⊢ (x_r : τ_r Γ) Σ e_r τ)
   -------------------------------------------------- "case"
   (⊢ Γ Σ (case e (inl x_l → e_l) (inr x_r → e_r)) τ)]

  [(⊢ Γ Σ e 0)
   ---------------------- "absurd"
   (⊢ Γ Σ (absurd τ e) τ)]

  [(⊢ Γ Σ e_1 τ)
   (⊢ Γ Σ e_2 τ)
   ---------------------- ";"
   (⊢ Γ Σ (e_1 || e_2) τ)])



(define eval
  (compatible-closure 
    (reduction-relation
      BANANA+SP
      #:domain e
      (--> ((λ (x τ) e_1) e_2)
           (substitute e_1 x e_2)
           "β")
      (--> (λ (x τ) (e x))
           e
           (side-condition (not (term (free-in x e))))
           "η")
      (--> (with (OP_i e_i) ... (η e_p) handle (η E e_v))
           (e_p e_v)
           "handle-η")
      (--> (with (OP_1 e_1) ... (OP_2 e_2) (OP_3 e_3) ... (η e_p) handle (OP_2 e_arg (λ (x τ) e_m)))
           ((e_2 e_arg) (λ (x τ) (with (OP_1 e_1) ... (OP_2 e_2) (OP_3 e_3) ... (η e_p) handle e_m)))
           (side-condition (term (no-match OP_2 (OP_1 ...))))
           "handle-OP")
      (--> (with (OP_i e_i) ... (η e_p) handle (OP e_arg (λ (x τ) e_m)))
           (OP e_arg (λ (x τ) (with (OP_i e_i) ... (η e_p) handle e_m)))
           (side-condition (term (no-match OP (OP_i ...))))
           "handle-missing-OP")
      (--> (♭ (η E e))
           e
           "♭")
      (--> (C (λ (x τ) (η E e)))
           (η E (λ (x τ) e))
           "𝓒-η")
      (--> (C (λ (x τ) (OP e_a (λ (x_k τ_k) e_k))))
           (OP e_a (λ (x_k τ_k) (C (λ (x τ) e_k))))
           (side-condition (not (term (free-in x e_a))))
           "𝓒-OP")
      (--> (π1 (pair e_1 e_2))
           e_1
           "β.×1")
      (--> (π2 (pair e_1 e_2))
           e_2
           "β.×2")
      (--> (case (inl E e) (inl x → e_l)
                           (inr y → e_r))
           (substitute e x e_l)
           "β.+1")
      (--> (case (inr E e) (inl x → e_l)
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





(define all-consts
  (term (⊤ : o
        (⊥ : o
        (¬ : (o → o)
        (∧ : (o → (o → o))
        (⇒ : (o → (o → o))
        (∨ : (o → (o → o))
        (∃ : ((ι → o) → o)
        (∀ : ((ι → o) → o)
        (= : (ι → (ι → o))
        (man : (ι → o)
        (woman : (ι → o)
        (Porsche : (ι → o)
        (Mercedes : (ι → o)
        (John : (ι → o)
        (Mary : (ι → o)
        (love : (ι → (ι → o))
        (own : (ι → (ι → o))
        (fascinate : (ι → (ι → o))
        (say : (ι → (o → o))
        (children : (ι → (ι → o))
        (best-friend : (ι → (ι → o))
        (nil : γ
        (::-ι : (ι → (γ → γ))
        (::-o : (o → (γ → γ))
        (++ : (γ → (γ → γ))
        (sel-he : (γ → ι)
        (sel-she : (γ → ι)
        (sel-it : (γ → ι)
        (selP : ((ι → o) → (γ → ι))
         ·)))))))))))))))))))))))))))))))

(define get-effect
  (term (GET : (1 ↦ γ)
         ·)))

(define drt-effects
  (term (FRESH : (1 ↦ ι)
        (PUSH : (ι ↦ 1)
        (ASSERT : (o ↦ 1)
        ,get-effect)))))

(define effects-no-scope
  (term (SPEAKER : (1 ↦ ι)
        (FRESH_I : (1 ↦ ι)
        (PUSH_I : (ι ↦ 1)
        (IMPLICATE : (o ↦ 1)
        (PRESUPPOSE : ((ι → (F ,drt-effects 1)) ↦ ι)
        ,drt-effects)))))))

(define all-effects
  (term (SCOPE : (((ι → (F ,effects-no-scope 1)) → (F ,effects-no-scope 1)) ↦ ι)
        ,effects-no-scope)))

(define (get-types env exp)
  (judgment-holds (⊢ ,env ,all-consts ,exp τ) τ))

(define (check-type exp type)
  (test-equal (get-types (term ·) exp) (list type)))

(define drs-handler
  (term (λ (A (F ,drt-effects 1)) (with
          (GET (λ (_ 1) (λ (k (γ → (F ,get-effect (γ → (F ,get-effect o)))))
                            (η ,get-effect (λ (e γ)
                                    (GET ★ (λ (e_ γ) (>>= (k ((++ e) e_))
                                                             (λ (f (γ → (F ,get-effect o))) (f e))))))))))
          (FRESH (λ (_ 1) (λ (k (ι → (F ,get-effect (γ → (F ,get-effect o)))))
                            (η ,get-effect (λ (e γ)
                                    (>>= (C (λ (x ι) (>>= (k x)
                                                          (λ (f (γ → (F ,get-effect o)))
                                                            (f e)))))
                                         (λ (pred (ι → o)) (η ,get-effect (∃ pred)))))))))
          (PUSH (λ (x ι) (λ (k (1 → (F ,get-effect (γ → (F ,get-effect o)))))
                            (η ,get-effect (λ (e γ)
                                    (>>= (k ★)
                                         (λ (f (γ → (F ,get-effect o)))
                                           (f ((::-ι x) e)))))))))
          (ASSERT (λ (p o) (λ (k (1 → (F ,get-effect (γ → (F ,get-effect o)))))
                             (η ,get-effect (λ (e γ)
                                     (>>= (k ★)
                                          (λ (f (γ → (F ,get-effect o)))
                                            (>>= (f ((::-o p) e))
                                                 (λ (q o) (η ,get-effect ((∧ p) q)))))))))))
          (η (λ (_ 1) (η ,get-effect (λ (e γ) (η ,get-effect ⊤)))))
          handle A))))

(check-type drs-handler (term ((F ,drt-effects 1) → (F ,get-effect (γ → (F ,get-effect o))))))

(define box
  (term (λ (A (F ,drt-effects 1))
          (>>= (,drs-handler A)
               (λ (f (γ → (F ,get-effect o))) (f nil))))))

(check-type box (term ((F ,drt-effects 1) → (F ,get-effect o))))

(define SI
  (term (λ (A (F ,all-effects 1)) (with
          (SCOPE (λ (c ((ι → (F ,effects-no-scope 1)) → (F ,effects-no-scope 1)))
                        (λ (k (ι → (F ,effects-no-scope 1)))
                          (c k))))
          (η (λ (x 1) (η ,effects-no-scope x)))
          handle A))))

(check-type SI (term ((F ,all-effects 1) → (F ,effects-no-scope 1))))