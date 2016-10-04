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
  (key ::= x c OP))

(define-metafunction BANANA
  different : any any -> #t or #f
  [(different any_1 any_1) #f]
  [(different any_1 any_2) #t])

(define-metafunction BANANA
  all-match : any (any ...) -> #t or #f
  [(all-match any_1 (any_1 any_more ...))
   (all-match any_1 (any_more ...))]
  [(all-match any_1 (any_2 any_more ...))
   #f]
  [(all-match any_1 ())
   #t])

(define-metafunction BANANA
  no-match : any (any ...) -> #t or #f
  [(no-match any_1 (any_1 any_more ...))
   #f]
  [(no-match any_1 (any_2 any_more ...))
   (no-match any_1 (any_more ...))]
  [(no-match any_1 ())
   #t])

(define-metafunction BANANA
  add/replace : key any context -> context
  [(add/replace key_1 any_1 ·)
   (key_1 : any_1 ·)]
  [(add/replace key_1 any_1 (key_1 : any_2 context_2))
   (key_1 : any_1 context_2)]
  [(add/replace key_1 any_1 (key_2 : any_2 context_2))
   (key_2 : any_2 (add/replace key_1 any_1 context_2))])

(define-metafunction BANANA
  merge : context context -> context
  [(merge · context_2)
   context_2]
  [(merge (key_1 : any_1 context_1) context_2)
   (add/replace key_1 any_1 (merge context_1 context_2))])

(define-metafunction BANANA
  ctx-from-ellipsis : ((key any) ...) -> context
  [(ctx-from-ellipsis ())
   ·]
  [(ctx-from-ellipsis ((key_1 any_1) (key_more any_more) ...))
   (key_1 : any_1 (ctx-from-ellipsis ((key_more any_more) ...)))])

(define-judgment-form
  BANANA
  #:mode (∈ I O I)
  #:contract (∈ key any context)
  
  [---------------------------------------
   (∈ key_1 any_1 (key_1 : any_1 context))]
  
  [(∈ key_1 any_1 context)
   (side-condition (different key_1 key_2))
   ---------------------------------------
   (∈ key_1 any_1 (key_2 : any_2 context))])

(define-judgment-form
  BANANA
  #:mode (context-included I I)
  #:contract (context-included context context)

  [------------------------------
   (context-included · context_2)]

  [(∈ key_1 any_1 context_2)
   (context-included context_1 context_2)
   ------------------------------------------------------
   (context-included (key_1 : any_1 context_1) context_2)])

(define-judgment-form
  BANANA
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
   (context-included E_in (merge E_out E))
   (side-condition (all-match τ_out (τ_out_h ...)))
   (side-condition (all-match E_out (E_out_h ...)))
   ------------------------------------------------------------ "handle"
   (⊢ Γ Σ (with (OP e_h) ... (η e_p) handle e) (F E_out τ_out))]
  
  [(⊢ Γ Σ e (τ_1 → (F E τ_2)))
   ------------------------------- "𝓒"
   (⊢ Γ Σ (C e) (F E (τ_1 → τ_2)))])


(define-metafunction BANANA
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
   (free-in x e)])

(define-metafunction BANANA
  subst : e x e -> e
  [(subst (e_f e_a) x e_new)
   ((subst e_f x e_new) (subst e_a x e_new))]
  [(subst (λ (x τ) e_body) x e_new)
   (λ (x τ) e_body)]
  [(subst (λ (x_arg τ) e_body) x e_new)
   ,(if (term (free-in x_arg e_new))
      (let ([x_f (variable-not-in (term (e_new e_body)) (term x_arg))])
        (term (λ (,x_f t) (subst (subst e_body x_arg ,x_f) x e_new))))
      (term (λ (x_arg t) (subst e_body x e_new))))]
  [(subst x x e_new)
   e_new]
  [(subst x_different x e_new)
   x_different]
  [(subst c x e_new)
   c]
  [(subst (η E e) x e_new)
   (η E (subst e x e_new))]
  [(subst (OP e_arg e_k) x e_new)
   (OP (subst e_arg x e_new) (subst e_k x e_new))]
  [(subst (with (OP_i e_i) ... (η e_p) handle e) x e_new)
   (with (OP_i (subst e_i x e_new)) ... (η (subst e_p x e_new))
         handle (subst e x e_new))]
  [(subst (C e) x e_new)
   (C (subst e x e_new))])

(define eval
  (compatible-closure 
   (reduction-relation
    BANANA
    #:domain e
    (--> ((λ (x τ) e_1) e_2)
         (subst e_1 x e_2)
         "β")
    (--> (C (λ (x τ) (η E e)))
         (η E (λ (x τ) e))
         "𝓒-η")
    (--> (C (λ (x τ) (OP e_a (λ (x_k τ_k) e_k))))
         (OP e_a (λ (x_k τ_k) (C (λ (x τ) e_k))))
         (side-condition (not (term (free-in x e_a))))
         "𝓒-OP")
    (--> (with (OP_i e_i) ... (η e_p) handle (η E e_v))
         (e_p e_v)
         "handle-η")
    (--> (with (OP_1 e_1) ... (OP_2 e_2) (OP_3 e_3) ... (η e_p) handle (OP_2 e_arg (λ (x τ) e_m)))
         ((e_2 e_arg) (λ (x_f τ) ((handler E_1 (OP_1 e_1) ... (OP_2 e_2) (OP_3 e_3) ... (η e_p)) (subst e_m x x_f))))
         (side-condition (term (no-match OP_2 (OP_1 ...))))
         (fresh x_f)
         "handle-OP")
    (--> (with (OP_i e_i) ... (η e_p) handle (OP e_arg (λ (x τ) e_m)))
         (OP e_arg (λ (x_f τ) (with (OP_i e_i) ... (η e_p) handle (subst e_m x x_f))))
         (side-condition (term (no-match OP (OP_i ...))))
         (fresh x_f)
         "handle-missing-OP"))
   BANANA
   e))

(define-metafunction BANANA
  >>= : e e -> e
  [(>>= e_m e_k)
   (with (η e_k) handle e_m)])

(define-judgment-form BANANA
  #:mode (α-equiv I I)
  
  [---------------------
   (α-equiv any any)]
  
  [(α-equiv any_1 any_2) ...
   -------------------------------------
   (α-equiv (any_1 ...) (any_2 ...))]

  [(where x_3 ,(variable-not-in (term (e_1 e_2)) (string->uninterned-symbol "x")))
   (α-equiv (subst e_1 x_1 x_3) (subst e_2 x_2 x_3))
   -------------------------------------------------------------------------------
   (α-equiv (λ (x_1 τ) e_1) (λ (x_2 τ) e_2))])


;; Typesetting the language definition

(define (render)
  (with-compound-rewriters (['no-match (λ (lws) (list "" (list-ref lws 2) " ∉ " (list-ref lws 3) ""))]
                            ['all-match (λ (lws) (list "" (list-ref lws 2) " = " (list-ref lws 3) ""))]
                            ['subst (λ (lws) (list "" (list-ref lws 2) "[" (list-ref lws 3) "/" (list-ref lws 4) "]"))]
                            ['⊢ (λ (lws) (list "" (list-ref lws 2) ", " (list-ref lws 3) ", " (list-ref lws 4) " ⊢ " (list-ref lws 5) " : " (list-ref lws 6) ""))]
                            ['∈ (λ (lws) (list "" (list-ref lws 2) " : " (list-ref lws 3) " ∈ " (list-ref lws 4) ""))]
                            ['free-in (λ (lws) (list "" (list-ref lws 2) " ∈ FV(" (list-ref lws 3) ")"))]
                            ['not (λ (lws) (list "¬(" (list-ref lws 2) ")"))])
      (with-atomic-rewriter 'C "𝓒"
        (begin (render-language BANANA "grammar.ps" #:nts (remove* '(context key) (language-nts BANANA)))
               (render-judgment-form ⊢ "typings.ps")
               (render-reduction-relation eval "reductions.ps")))))




(define all-consts
  (term (★ : u
        (⊤ : o
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
        (::_ι : (ι → (γ → γ))
        (::_o : (o → (γ → γ))
        (++ : (γ → (γ → γ))
        (sel_he : (γ → ι)
        (sel_she : (γ → ι)
        (sel_it : (γ → ι)
        (selP : ((ι → o) → (γ → ι))
         ·))))))))))))))))))))))))))))))))

(define get-effect
  (term (GET : (u ↦ γ)
         ·)))

(define drt-effects
  (term (FRESH : (u ↦ ι)
        (PUSH : (ι ↦ u)
        (ASSERT : (o ↦ u)
        ,get-effect)))))

(define effects-no-scope
  (term (SPEAKER : (u ↦ ι)
        (FRESH_I : (u ↦ ι)
        (PUSH_I : (ι ↦ u)
        (IMPLICATE : (o ↦ u)
        (PRESUPPOSE : ((ι → (F ,drt-effects u)) ↦ ι)
        ,drt-effects)))))))

(define all-effects
  (term (SCOPE : (((ι → (F ,effects-no-scope u)) → (F ,effects-no-scope u)) ↦ ι)
        ,effects-no-scope)))

(define (get-types env exp)
  (judgment-holds (⊢ ,env ,all-consts ,exp τ) τ))

(define (check-type exp type)
  (test-equal (get-types (term ·) exp) (list type)))

(define drs-handler
  (term (λ (A (F ,drt-effects u)) (with
          (GET (λ (_ u) (λ (k (γ → (F ,get-effect (γ → (F ,get-effect o)))))
                            (η ,get-effect (λ (e γ)
                                    (GET ★ (λ (e_ γ) (>>= (k ((++ e) e_))
                                                             (λ (f (γ → (F ,get-effect o))) (f e))))))))))
          (FRESH (λ (_ u) (λ (k (ι → (F ,get-effect (γ → (F ,get-effect o)))))
                            (η ,get-effect (λ (e γ)
                                    (>>= (C (λ (x ι) (>>= (k x)
                                                          (λ (f (γ → (F ,get-effect o)))
                                                            (f e)))))
                                         (λ (pred (ι → o)) (η ,get-effect (∃ pred)))))))))
          (PUSH (λ (x ι) (λ (k (u → (F ,get-effect (γ → (F ,get-effect o)))))
                            (η ,get-effect (λ (e γ)
                                    (>>= (k ★)
                                         (λ (f (γ → (F ,get-effect o)))
                                           (f ((::_ι x) e)))))))))
          (ASSERT (λ (p o) (λ (k (u → (F ,get-effect (γ → (F ,get-effect o)))))
                             (η ,get-effect (λ (e γ)
                                     (>>= (k ★)
                                          (λ (f (γ → (F ,get-effect o)))
                                            (>>= (f ((::_o p) e))
                                                 (λ (q o) (η ,get-effect ((∧ p) q)))))))))))
          (η (λ (_ u) (η ,get-effect (λ (e γ) (η ,get-effect ⊤)))))
          handle A))))

(check-type drs-handler (term ((F ,drt-effects u) → (F ,get-effect (γ → (F ,get-effect o))))))

(define box
  (term (λ (A (F ,drt-effects u))
          (>>= (,drs-handler A)
               (λ (f (γ → (F ,get-effect o))) (f nil))))))

(check-type box (term ((F ,drt-effects u) → (F ,get-effect o))))

(define SI
  (term (λ (A (F ,all-effects u)) (with
          (SCOPE (λ (c ((ι → (F ,effects-no-scope u)) → (F ,effects-no-scope u)))
                        (λ (k (ι → (F ,effects-no-scope u)))
                          (c k))))
          (η (λ (x u) (η ,effects-no-scope x)))
          handle A))))

(check-type SI (term ((F ,all-effects u) → (F ,effects-no-scope u))))