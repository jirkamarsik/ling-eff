#lang racket
(require redex)
(require (for-syntax racket/syntax))

;; Below is a mechanization of the lambda-banana calculus defined in
;; 'Effects and Handlers in Natural Language'. The mechanization can be
;; consulted to verify the computations done in the dissertation and see a
;; formalized definition of the calculus and the grammar.  Beware that the
;; implementation of normalization is very inefficient and it can thus take
;; an hour to normalize a term large enough to represent an interesting
;; linguistic example.


;; Defining the Calculus
;; =====================
;; 
;; These are the terms of the lambda-banana calculus, as defined in Section
;; 1.2 of the dissertation.
(define-language BANANA
  (e ::= x
         c
         (e e)
         (λ (x) e)
         (η e)
         (OP e (λ (x) e))
         ;; Since we cannot (easily) change the delimiters from parentheses
         ;; to banana brackets, we employ a different notation in this
         ;; implementation.
         (with (OP e) ... (η e) handle e)
         ;; DrRacket does not have a convenient shortcut for a cherry
         ;; symbol and so we use ♭.
         (♭ e)
         (C e))
  (x ::= variable-not-otherwise-mentioned)
  (c ::= variable-not-otherwise-mentioned)
  (OP ::= variable-not-otherwise-mentioned))

;; We then extend the set of terms with the constructions for sum types and
;; product types from Section 1.4 of the dissertation.
(define-extended-language BANANA+SP
  BANANA
  (e ::= ....
         ★
         (π1 e)
         (π2 e)
         (pair e e)
         (inl e)
         (inr e)
         (case e e e)
         (absurd e)))


;; Finally, we add the ambiguity operator that we introduced in Subsection 7.3.4
;; of the dissertation. Since semicolon is used by Racket to indicate
;; comments, we use || as the symbol.
(define-extended-language BANANA+SPA
  BANANA+SP
  (e ::= ....
         (e || e)))

;; We define a few necessary metafunctions on the terms of our calculus.

;; (no-match x (y ...)) is true iff x is different from all y ...
(define-metafunction BANANA+SPA
  no-match : any (any ...) -> #t or #f
  [(no-match any_1 (any_1 any_more ...))
   #f]
  [(no-match any_1 (any_2 any_more ...))
   (no-match any_1 (any_more ...))]
  [(no-match any_1 ())
   #t])

;; (free-in x e) is true iff x occurs free in e
(define-metafunction BANANA+SPA
  free-in : x e -> #t or #f
  [(free-in x x)
   #t]
  [(free-in x x_different)
   #f]
  [(free-in x c)
   #f]
  [(free-in x (e_f e_a))
   ,(or (term (free-in x e_f)) (term (free-in x e_a)))]
  [(free-in x (λ (x) e))
   #f]
  [(free-in x (λ (x_different) e))
   (free-in x e)]
  [(free-in x (η e))
   (free-in x e)]
  [(free-in x (OP e_arg (λ (x_r) e_k)))
   ,(or (term (free-in x e_arg)) (term (free-in x e_k)))]
  [(free-in x (with (OP_i e_i) ... (η e_p) handle e))
   ,(or (ormap identity (term ((free-in x e_i) ...)))
        (term (free-in x e_p))
        (term (free-in x e)))]
  [(free-in x (♭ e))
   (free-in x e)]
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
  [(free-in x (case e e_l e_r))
   ,(or (term (free-in x e))
        (term (free-in x e_l))
        (term (free-in x e_r)))]
  [(free-in x (absurd e))
   (free-in x e)]
  [(free-in x (e_1 || e_2))
   ,(or (term (free-in x e_1)) (term (free-in x e_2)))])

;; (subst e x e_new) is the result of substituting e_new for all the free
;; occurrences of x in e (i.e. e[x := e_new])
(define-metafunction BANANA+SPA
  subst : e x e -> e
  [(subst x x e_new)
   e_new]
  [(subst x_different x e_new)
   x_different]
  [(subst c x e_new)
   c]
  [(subst (e_f e_a) x e_new)
   ((subst e_f x e_new) (subst e_a x e_new))]
  [(subst (λ (x) e_body) x e_new)
   (λ (x) e_body)]
  [(subst (λ (x_arg) e_body) x e_new)
   ,(if (term (free-in x_arg e_new))
      (let ([x_f (variable-not-in (term (e_new e_body)) (term x_arg))])
        (term (λ (,x_f) (subst (subst e_body x_arg ,x_f) x e_new))))
      (term (λ (x_arg) (subst e_body x e_new))))]
  [(subst (η e) x e_new)
   (η (subst e x e_new))]
  [(subst (OP e_arg e_k) x e_new)
   (OP (subst e_arg x e_new) (subst e_k x e_new))]
  [(subst (with (OP_i e_i) ... (η e_p) handle e) x e_new)
   (with (OP_i (subst e_i x e_new)) ... (η (subst e_p x e_new))
         handle (subst e x e_new))]
  [(subst (♭ e) x e_new)
   (♭ (subst e x e_new))]
  [(subst (C e) x e_new)
   (C (subst e x e_new))]
  [(subst ★ x e_new)
   ★]
  [(subst (π1 e) x e_new)
   (π1 (subst e x e_new))]
  [(subst (π2 e) x e_new)
   (π2 (subst e x e_new))]
  [(subst (pair e_1 e_2) x e_new)
   (pair (subst e_1 x e_new) (e_2 x e_new))]
  [(subst (inl e) x e_new)
   (inl (subst e x e_new))]
  [(subst (inr e) x e_new)
   (inr (subst e x e_new))]
  [(subst (case e e_l e_r) x e_new)
   (case (subst e x e_new) (subst e_l x e_new) (subst e_r x e_new))]
  [(subst (absurd e) x e_new)
   (absurd (subst e x e_new))]
  [(subst (e_1 || e_2) x e_new)
   ((subst e_1 x e_new) || (subst e_2 x e_new))])

;; We can now define the reduction relation of our calculus. This follows
;; closely the definitions given in Chapter 1 of the dissertation.
(define reduce
  (compatible-closure 
    (reduction-relation
      BANANA+SPA
      #:domain e
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
           "β.+2"))
    BANANA+SPA
    e))






;; Anaphora Resolution
;; ===================
;;
;; When computing the normal forms of the terms in our dissertation, we
;; often assume that the anaphora resolution operators sel_he, sel_she,
;; sel_it and selP choose some specific individual from the context, or in
;; the case of selP, recognize that the context does not contain any
;; suitable individual and reduce to some value which signals this. We will
;; want to use our mechanization to reduce lambda-banana terms to readable
;; truth-conditions and so we include reduction rules that implement a very
;; basic form of anaphora resolution into the reduction relation of our
;; calculus.

;; We extend our formal language with gender markers.
(define-extended-language BANANA+SPAC
  BANANA+SPA
  (gender ::= masculine
              feminine
              neutral))

;; (individual-in i c)
;; iff i is an individual available in the context c
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

;; (proposition-in p c)
;; iff p is a proposition asserted in the context c
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

;; (has-gender i g c)
;; iff we can infer that i has gender g in the context c
(define-judgment-form
  BANANA+SPAC
  #:mode (has-gender I I I)
  #:contract (has-gender e gender e)

  [(proposition-in (John* e_x) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in (Jones* e_x) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in (Bill* e_x) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in (Socrates* e_x) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in (man* e_x) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in (therapist* e_x) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in (farmer* e_x) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in (Mary* e_x) e_c)
   -----------------------------
   (has-gender e_x feminine e_c)]

  [(proposition-in (Sarah* e_x) e_c)
   -----------------------------
   (has-gender e_x feminine e_c)]

  [(proposition-in (woman* e_x) e_c)
   -----------------------------
   (has-gender e_x feminine e_c)]

  [(proposition-in (therapist* e_x) e_c)
   ------------------------------
   (has-gender e_x feminine e_c)]

  [(proposition-in (farmer* e_x) e_c)
   ------------------------------
   (has-gender e_x feminine e_c)]

  [(proposition-in (Ulysses* e_x) e_c)
   ----------------------------
   (has-gender e_x neutral e_c)]
  
  [(proposition-in (Porsche* e_x) e_c)
   ----------------------------
   (has-gender e_x neutral e_c)]

  [(proposition-in (Mercedes* e_x) e_c)
   ----------------------------
   (has-gender e_x neutral e_c)]

  [(proposition-in (dog* e_x) e_c)
   ----------------------------
   (has-gender e_x neutral e_c)]

  [(proposition-in (unicorn* e_x) e_c)
   ----------------------------
   (has-gender e_x neutral e_c)]

  [(proposition-in (siamese-cat* e_x) e_c)
   ----------------------------
   (has-gender e_x neutral e_c)]

  [(proposition-in (donkey* e_x) e_c)
   ----------------------------
   (has-gender e_x neutral e_c)]

  [(proposition-in (vehicle* e_x) e_c)
   ----------------------------
   (has-gender e_x neutral e_c)]

  [(proposition-in ((best-friend* e_x) e_y) e_c)
   ------------------------------
   (has-gender e_x masculine e_c)]

  [(proposition-in ((best-friend* e_x) e_y) e_c)
   ------------------------------
   (has-gender e_x feminine e_c)]

  [(proposition-in ((mother* e_x) e_y) e_c)
   ------------------------------
   (has-gender e_x feminine e_c)])

;; (sel g c i)
;; iff i is an available individual of gender g in the context c
(define-judgment-form
  BANANA+SPAC
  #:mode (sel I I O)
  #:contract (sel gender e e)

  [(individual-in e_referent e_context)
   (has-gender e_referent gender e_context)
   ---------------------------------
   (sel gender e_context e_referent)])

;; (all-conds-in p c)
;; iff p can be decomposed into a conjunction of propositions
;; that are all included in the context c
(define-judgment-form
  BANANA+SPAC
  #:mode (all-conds-in I I)
  #:contract (all-conds-in e e)

  [--------------------------
   (all-conds-in ⊤ e_context)]
  
  [(all-conds-in e_c1 e_context)
   (all-conds-in e_c2 e_context)
   ----------------------------------------
   (all-conds-in ((∧ e_c1) e_c2) e_context)]

  [(proposition-in e_condition e_context)
   ------------------------------------
   (all-conds-in e_condition e_context)])

;; (sel-prop p c i)
;; iff i is an individual accessible in the context c and which, according
;; to the context c, satisfies the predicate p
(define-judgment-form
  BANANA+SPAC
  #:mode (sel-prop I I O)
  #:contract (sel-prop e e e)

  [(individual-in e_referent e_context)
   (all-conds-in (subst e_condition x e_referent) e_context)
   -----------------------------------------------------
   (sel-prop (λ (x) e_condition) e_context e_referent)]

  [(individual-in e_referent e_context)
   (all-conds-in (e_property e_referent) e_context)
   ------------------------------------------
   (sel-prop e_property e_context e_referent)])

;; (complete-ctx c)
;; iff c is a context built only from nil, ++, ::-ι and ::-o
;; (i.e. all of its elements are fixed, unlike e.g. (x ::-ι e))
(define-judgment-form
  BANANA+SPAC
  #:mode (complete-ctx I)
  #:contract (complete-ctx e)

  [------------------
   (complete-ctx nil)]

  [(complete-ctx e_ctx1)
   (complete-ctx e_ctx2)
   -----------------------------------
   (complete-ctx ((++ e_ctx1) e_ctx2))]

  [(complete-ctx e_ctx)
   -----------------------------------
   (complete-ctx ((::-ι e_ind) e_ctx))]
  
  [(complete-ctx e_ctx)
   ------------------------------------
   (complete-ctx ((::-o e_prop) e_ctx))])

;; reduce-more extends the reduction relation 'reduce of our calculus. It
;; adds rules that concatenate contexts and look within them for anaphoric
;; antecedents.
(define reduce-more
  (compatible-closure
    (extend-reduction-relation reduce
      BANANA+SPAC
      #:domain e
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
           (inl e_referent)
           (judgment-holds (sel-prop e_property e_context e_referent))
           "selP-found")
      (--> ((selP e_property) e_context)
           (inr ★)
           (judgment-holds (complete-ctx e_context))
           (side-condition (not (judgment-holds (sel-prop e_property
                                                          e_context
                                                          e_referent))))
           "selP-not-found"))
    BANANA+SPAC
    e))






;; Manipulating Terms
;; ==================
;;
;; Defined below are utility functions that allow us to normalize and
;; pretty-print terms.

;; We enable caching of metafunctions in hopes to squeeze out some extra
;; performance.
(caching-enabled? #t)
(set-cache-size! 1000000)

;; normalize uses the apply-reduction-relation of Redex to find a normal
;; form for a lambda-banana term.
(define (normalize rel t)
  (let [(steps (apply-reduction-relation rel t))]
    (if (null? steps)
      t
      (normalize rel (car steps)))))

;; map-children maps a function over the immediate subterms of a term. In
;; Haskell parlance, this is the Functor instance for lambda-banana terms.
(define map-children-aux
  (term-match/single BANANA+SPA
    [x
     (λ (f) (term x))]
    [c
     (λ (f) (term c))]
    [(e_1 e_2)
     (λ (f) (term (,(f (term e_1)) ,(f (term e_2)))))]
    [(λ (x) e)
     (λ (f) (term (λ (x) ,(f (term e)))))]
    [(η e)
     (λ (f) (term (η ,(f (term e)))))]
    [(OP e_1 (λ (x) e_2))
     (λ (f) (term (OP ,(f (term e_1)) (λ (x) ,(f (term e_2))))))]
    [(with (OP e_h) ... (η e_p) handle e)
     (λ (f) (term (with ,@(map (λ (c) (list (car c) (f (cadr c))))
                               (term ((OP e_h) ...)))
                        (η ,(f (term e_p)))
                     handle ,(f (term e)))))]
    [(♭ e)
     (λ (f) (term (♭ ,(f (term e)))))]
    [(C e)
     (λ (f) (term (C ,(f (term e)))))]
    [★
     (λ (f) (term ★))]
    [(π1 e)
     (λ (f) (term (π1 ,(f (term e)))))]
    [(π2 e)
     (λ (f) (term (π2 ,(f (term e)))))]
    [(pair e_1 e_2)
     (λ (f) (term (pair ,(f (term e_1)) ,(f (term e_2)))))]
    [(inl e)
     (λ (f) (term (inl ,(f (term e)))))]
    [(inr e)
     (λ (f) (term (inr ,(f (term e)))))]
    [(case e e_l e_r)
     (λ (f) (term (case ,(f (term e))
                        ,(f (term e_l))
                        ,(f (term e_r)))))]
    [(absurd e)
     (λ (f) (term (absurd ,(f (term e)))))]
    [(e_1 || e_2)
     (λ (f) (term (,(f (term e_1)) || ,(f (term e_2)))))]))

(define (map-children f t)
  ((map-children-aux t) f))

;; normalize-bottom-up traverses a term bottom-up and normalizes
;; it. Normalization often makes a term smaller, which increases the
;; performance of identifying redexes and therefore leads to faster
;; normalization times.
(define (normalize-bottom-up rel t)
  (normalize rel (map-children (λ (x) (normalize-bottom-up rel x)) t)))


;; simplify-logic is a reduction relation that implements some simple
;; logical rules.  Their point is to sanitize the logical formulas
;; generated by our system by, e.g., decoding the logical operators ∀, ⇒
;; and ∨.
(define simplify-logic
  (compatible-closure
    (reduction-relation
      BANANA+SPA
      #:domain e
      (--> ((∧ e) ⊤)
           e)
      (--> ((∧ ⊤) e)
           e)
      (--> (¬ (¬ e))
           e)
      (--> (¬ (∃ (λ (x) e)))
           (∀ (λ (x) (¬ e))))
      (--> (¬ (∀ (λ (x) e)))
           (∃ (λ (x) (¬ e))))
      (--> (¬ ((∧ e_1) (¬ e_2)))
           ((⇒ e_1) e_2))
      (--> (¬ ((∧ e_1) (∀ (λ (x) (¬ e_2)))))
           ((⇒ e_1) (∃ (x) e_2)))
      (--> (¬ ((∧ (¬ e_1)) (¬ e_2)))
           ((∨ e_1) e_2)))
    BANANA+SPA
    e))

;; prettify-logic makes logical operators infix and translates
;; lambda-binders to quantifiers. Since the result of this translation is
;; no longer a valid term in our calculus, we have to define a new notion
;; of context closure.
(define-extended-language BANANA+SPAL
  BANANA+SPA
  (context ::= hole
               (any_1 ... context any_2 ...)))

(define prettify-logic
  (context-closure
    (reduction-relation
      BANANA+SPA
      (--> ((∧ any_1) any_2)
           (any_1 ∧ any_2))
      (--> ((⇒ any_1) any_2)
           (any_1 ⇒ any_2))
      (--> ((∨ any_1) any_2)
           (any_1 ∨ any_2))
      (--> (∃ (λ (x) any))
           (∃ (x) any))
      (--> (∀ (λ (x) any))
           (∀ (x) any))
      (--> ((c_pred any_1 ...) any_2)
           (c_pred any_1 ... any_2)
           ;; We translate the convention of using boldface to typeset
           ;; logical predicates in the dissertation to the convention of
           ;; using symbols ending with * in this mechanization.
           (side-condition (string-suffix? (symbol->string (term c_pred)) "*"))))
    BANANA+SPAL
    context))

;; compute-truth-conditions combines all the steps necessary to go from
;; a lambda-banana term which encodes the meaning of a sentence to
;; human-readable truth-conditions of that sentence.
(define (compute-truth-conditions term)
  (let* ([normal-form (normalize-bottom-up reduce-more term)]
         [simplified (normalize simplify-logic normal-form)]
         [pretty (normalize prettify-logic simplified)])
    pretty))

;; term? verifies whether a Redex term is a lambda-banana term (i.e. does
;; it conform to the grammar of this formalization).
(define term? (term-match/single BANANA+SPA [e #t] [_ #f]))

;; (check-term t) is a unit test that checks whether is a valid term of our
;; calculus.
(define (check-term t)
  (test-equal (term? t) #t))

;; define-checked-term extends Redex's define-term by checking whether
;; every defined term conforms to the grammar.
(define-syntax-rule (define-checked-term name body)
  (begin
    (define-term name body)
    (check-term (term name))))

;; find-broken-form is a debugging utility. If a term is not accepted by
;; the grammar as a valid verm, find-broken-form helps us to find the
;; minimal subterm which is malformed. term-children is an auxiliary
;; function that allows us to recover the immediate subterms of a malformed
;; term.
(define term-children
  (term-match BANANA+SPA
    [variable                 (term ())]
    [(variable any)           (term (any))]
    [((any_1 ...) any_2)      (term ((any_1 ...) any_2))]
    [(λ (x) any)              (term (any))]
    [(OP any_1 (λ (x) any_2)) (term (any_1 any_2))]
    [(with (OP any_h) ...
           (η any_p)
       handle any)            (term (any_h ... any_p any))]
    [(pair any_1 any_2)       (term (any_1 any_2))]
    [(case any any_l any_r)   (term (any any_l any_r))]))

(define (find-broken-form tree)
  (let ([matches (term-children tree)])
    (if (null? matches)
      tree
      (let* ([children     (first matches)]
             [bad-children (filter (λ (x) (not (term? x))) children)])
        (if (null? bad-children)
          tree
          (find-broken-form (first bad-children)))))))




 


;; Common Combinators
;; ==================
;;
;; This part mirrors Section 1.6 of the dissertation. It introduces
;; syntactic shortcuts, combinators that we will make heavy use of.


;; We define the monadic bind (>>=) of our monad.
(define-metafunction BANANA+SPA
  >>= : e e -> e
  [(>>= e_m e_k)
   (with (η e_k) handle e_m)])

;; The op! syntax lets uses an operation with the trivial continuation
;; (lambda x. eta x).
(define-metafunction BANANA+SPA
  [(! OP)
   (λ (x) (OP x (λ (y) (η y))))]
  [(! OP e)
   (OP e (λ (x) (η x)))])

;; We functionalize OP, i.e. we turn the OP expression constructor into a
;; function expression. Also known as a generic effect.
(define-metafunction BANANA+SPA
  gen : OP -> e
  [(gen OP)
   (λ (x) (λ (k) (OP x (λ (y) (k y)))))])

;; This construction lets us omit the eta clause when writing
;; a handler. The default clause eta: (lambda x. eta x) is used.
(define-metafunction BANANA+SPA
  with-η : (OP e) ... handle e -> e
  [(with-η (OP e_h) ... handle e_arg)
   (with (OP e_h) ... (η (λ (x) (η x))) handle e_arg)])

;; We functionalize handlers. In lambda-banana, this corresponds to writing
;; a handler without giving its argument.
(define-metafunction BANANA+SPA
  handler : (OP e) ... (η e) -> e
  [(handler (OP e_h) ... (η e_p))
   (λ (x) (with (OP e_h) ... (η e_p) handle x))])

;; We combine the two last abstractions to define a functionalized handler
;; expression with the default eta clause.
(define-metafunction BANANA+SPA
  handler-η : (OP e) ... -> e
  [(handler-η (OP e_h) ...)
   (λ (x) (with-η (OP e_h) ... handle x))])

;; We define a syntax for (n-ary) function composition.
(define-metafunction BANANA+SPA
  ∘ : e ... -> e
  [(∘)
   (λ (x) x)]
  [(∘ e)
   e]
  [(∘ e_f e_g)
   (λ (x) (e_f (e_g x)))]
  [(∘ e_1 e_2 e_more ...)
   (∘ (∘ e_1 e_2) e_more ...)])

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

;; We define function application for cases when the function is provided
;; by a computation.
(define-metafunction BANANA+SPA
  <<· : e e -> e
  [(<<· e_f e_x)
   (>>= e_f (λ (f) (η (f e_x))))])

;; We also define function application when the argument is the result of
;; a computation.
(define-metafunction BANANA+SPA
  ·>> : e e -> e
  [(·>> e_f e_x)
   (>>= e_x (λ (x) (η (e_f x))))])

;; Finally, we define function application for when both function and
;; argument are the results of computations. This is the <*> binary
;; operator of applicative functors.
(define-metafunction BANANA+SPA
  <<·>> : e e -> e
  [(<<·>> e_f e_x)
   (>>= e_f (λ (f) (>>= e_x (λ (x) (η (f x))))))])

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

;; When defining the open handler for dynamics (box), we will make use of
;; the following two combinators, introduced in Subsection 7.3.1 of
;; the dissertation.
(define-metafunction BANANA+SPA
  <<<· : e e -> e
  [(<<<· e_f e_x)
   (>>= e_f (λ (f) (f e_x)))])

(define-metafunction BANANA+SPA
  ∃>> : e -> e
  [(∃>> e_pred)
   (·>> ∃ (C e_pred))])






;; Handlers
;; ========
;;
;; The rest of the program will cover the final grammar presented in
;; Chapter 8. We start by first regrouping the definitions of all the
;; handlers.

;; This is the box handler for dynamics, based on its presentation in
;; Section 8.1.  Note that the INTRODUCE operation has been decomposed into
;; FRESH and PUSH as in Subsection 8.5.1.
(define-checked-term box
  (λ (A)
    (<<<· ((handler
      (GET (λ (_) (λ (k)
             (η (λ (e) (GET ★ (λ (e_) (<<<· (k ((++ e) e_)) e))))))))
      (FRESH (λ (_) (λ (k)
               (η (λ (e) (∃>> (λ (x) (<<<· (k x) e))))))))
      (PUSH (λ (x) (λ (k)
              (η (λ (e) (<<<· (k ★) ((::-ι x) e)))))))
      (ASSERT (λ (p) (λ (k)
                (η (λ (e) (∧>> p (<<<· (k ★) ((::-o p) e))))))))
      (η (λ (_) (η (λ (e) (η ⊤)))))) A) nil)))

;; We have replaced INTRODUCE by FRESH and PUSH and so we express INTRODUCE
;; in terms of FRESH and PUSH.
(define-metafunction BANANA+SPA
  INTRODUCE : e e -> e
  [(INTRODUCE e_u e_k)
     (FRESH e_u (λ (x)
     (PUSH x (λ (y)
     (e_k x)))))])

;; The empty handler (Section 8.1) evaluates the discourse in an empty
;; anaphoric context.
(define-checked-term empty
  (handler-η (GET (λ (_) (λ (k) (k nil))))))

;; SI, which stands for Scope Island, is the handler for SCOPE effects,
;; which are used for quantification (Section 8.5).
(define-checked-term SI
  (handler-η (SCOPE (λ (c) (λ (k) (c k))))))

;; Next, we turn to presupposition (Section 8.2). We have the accommodate
;; handler, that accommodates presuppositions by introducing new discourse
;; referents.  Note that the predicate P is assumed to yield a computation
;; with DRT effects (GET, FRESH, PUSH, ASSERT) and not just a plain truth
;; value. This is to licence anaphoric binding from definite descriptions,
;; as in Subsection 8.6.2.
(define-checked-term accommodate
  (handler-η (PRESUPPOSE (λ (P) (λ (k)
               (INTRODUCE ★ (λ (x) (>>= (P x) (λ (_) (k x))))))))))

;; We will need to make a non-deterministic choice when trying to
;; accommodate a presupposition at different levels. The choose expression
;; constructor, which corresponds to the + operator in the dissertation
;; (Section 8.2), gives us a convenient syntax for the choice operation AMB
;; : 1 → 2.
(define-metafunction BANANA+SPA
  choose : e e -> e
  [(choose e_1 e_2)
   (AMB ★ (λ (b) (ifte b e_1 e_2)))])

;; The maybeAccommodate handler uses choose to consider both projecting the
;; presupposition and accommodating it.
(define-checked-term maybeAccommodate
  (handler-η (PRESUPPOSE (λ (P) (λ (k)
               (choose (PRESUPPOSE P (λ (x) (k x)))
                       (INTRODUCE ★ (λ (x) (>>= (P x) (λ (_) (k x)))))))))))

;; The find combinator is of the same type as (! PRESUPPOSE). It tries to
;; look for the missing entity in the context. If it cannot be found, it
;; projects the presupposition. Note that this find is the one from
;; Subsection 8.6.2, which expects dynamic predicates as arguments and uses
;; ♭ ∘ empty ∘ box to make them static.
(define-checked-term find
  (λ (P) (GET ★ (λ (e) (case ((selP (λ (x) (♭ (empty (box (P x)))))) e)
                         (λ (x) (η x))
                         (λ (_) (! PRESUPPOSE P)))))))

;; The useFind handler tries resolving the presuppositions within its
;; arguments using find.
(define-checked-term useFind
  (handler-η (PRESUPPOSE (λ (P) (λ (k) (>>= (find P) k))))))

;; maybeAccommodate introduces ambiguity via the AMB operator. The search
;; handler resolves the ambiguity by choosing which of the two
;; possibilities to pursue.  In the dissertation, we make this choice based
;; on whether or not the computations fail.  In this mechanization, we
;; leave the ambiguity operator unresolved.
(define-checked-term search
  (handler-η (AMB (λ (_) (λ (k) ((k true) || (k false)))))))

;; We incorporate the possibility to accommodate a presupposition in every
;; DRS on the projection line by introducing maybeAccommodate to the box
;; handler. We also add useFind so that presuppositions can be (preferably)
;; found within the context without having to be accommodated. We will
;; still need to use the original box handler and so we name this one dbox
;; (in Chapter 7 of the dissertation, we used 'box with a bar on top).
(define-checked-term dbox
  (∘ box maybeAccommodate useFind))

;; When extending our treatment of presuppositions to complex definite
;; descriptions (e.g. when dealing with restrictive relative clauses) in
;; Subsection 8.6.2, we introduced a series of handlers which are applied
;; to an effectful predicate before it is projected as a presupposition.

;; inTheContext evaluates its argument in a given anaphoric context. This
;; is used so that even when the predicate ends up being interpreted in
;; some higher context, it still has access to both the referents available
;; in its context and those introduced within the predicate.
(define-checked-term inTheContext
  (λ (e) (handler-η (GET (λ (_) (λ (k) (GET ★ (λ (e_) (k ((++ e) e_))))))))))

;; separateDynamics delays the execution of all dynamic effects (GET,
;; INTRODUCE (i.e. FRESH and PUSH), and ASSERT).
(define-checked-term separateDynamics
  (handler (GET (λ (x) (λ (k) (·>> ((gen GET) x) (C k)))))
           (FRESH (λ (x) (λ (k) (·>> ((gen FRESH) x) (C k)))))
           (PUSH (λ (x) (λ (k) (·>> ((gen PUSH) x) (C k)))))
           (ASSERT (λ (x) (λ (k) (·>> ((gen ASSERT) x) (C k)))))
           (η (λ (x) (η (η x))))))

;; packageProperty takes an effectful property (e.g. the meaning of
;; a complex noun), evaluates some of its effects and produces a property
;; whose only effects are dynamic.
(define-checked-term packageProperty
  (λ (P) (GET ★ (λ (e)
         (C (λ (x) (separateDynamics ((inTheContext e) (maybeAccommodate (SI (P x)))))))))))

;; The next two handlers are the handlers for conventional implicature from
;; Section 8.3.  The asImplicature handler translates ASSERT to IMPLICATE
;; and INTRODUCE (i.e. FRESH and PUSH) to INTRODUCE_I (i.e. FRESH_I and
;; PUSH_I).
(define-checked-term asImplicature
  (handler-η (FRESH (gen FRESH_I))
             (PUSH (gen PUSH_I))
             (ASSERT (gen IMPLICATE))))

;; The withImplicatures handler reintegrates conventional implicatures into
;; the layer of the main asserted meaning by reversing the translation done
;; by asImplicature.
(define-checked-term withImplicatures
  (handler-η (FRESH_I (gen FRESH))
             (PUSH_I (gen PUSH))
             (IMPLICATE (gen ASSERT))))

;; withSpeaker is the handler for first-person pronouns from Section 8.4.
(define-checked-term withSpeaker
  (λ (s) (handler-η (SPEAKER (λ (_) (λ (k) (k s)))))))

;; Finally, we can compose all of the handlers to get an interpreter that
;; maps any computation in our fragment to a proposition.
(define-checked-term top
  (λ (s)
    (∘ search empty box accommodate useFind withImplicatures (withSpeaker s) SI)))





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
   (>>= e_a (λ (x_) e_b))])

(define-metafunction BANANA+SPA
  d¬ : e -> e
  [(d¬ e_a)
   (>>= (dbox e_a) (λ (a) (! ASSERT (¬ a))))])

(define-metafunction BANANA+SPA
  d∃ : e -> e
  [(d∃ e_pred)
   (INTRODUCE ★ (λ (x) (e_pred x)))])

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






;; Grammar
;; =======
;;
;; What follows are lambda-banana terms which are the interpretations of
;; the lexical items that make up our grammar. This grammar combines all of
;; the phenomena discussed in Chapter 8 of the dissertation.

;; she : NP
(define-checked-term she
  (GET ★ (λ (e)
  (η (sel-she e)))))

;; he : NP
(define-checked-term he
  (GET ★ (λ (e)
  (η (sel-he e)))))

;; it : NP
(define-checked-term it
  (GET ★ (λ (e)
  (η (sel-it e)))))

;; common-noun : N
;; Common nouns all have the same kind of meaning and so we define a macro
;; to facilitate the population of the lexicon.
(define-syntax-rule (define-common-noun abstract object)
  (define-checked-term abstract
    (λ (x) (! ASSERT (object x)))))

(define-common-noun man man*)
(define-common-noun woman woman*)
(define-common-noun therapist therapist*)
(define-common-noun dog dog*)
(define-common-noun unicorn unicorn*)
(define-common-noun siamese-cat siamese-cat*)
(define-common-noun Porsche Porsche*)
(define-common-noun Mercedes Mercedes*)
(define-common-noun farmer farmer*)
(define-common-noun donkey donkey*)
;; We use vehicle instead of car so as not to shadow Racket's car.
(define-common-noun vehicle vehicle*)

;; indef : N → NP
;; This is the semantics of the indefinite article. In the dissertation, we
;; call this constructor 'a. Here we give it a longer name so as to avoid
;; confusion with the variable 'a.
(define-checked-term indef
  (λ (n) (INTRODUCE ★ (λ (x)
         (>>= (n x) (λ (_)
         (η x)))))))

;; transitive-verb : NP → NP → S
(define-syntax-rule (define-transitive-verb abstract object)
  (define-checked-term abstract
    (λ (O) (λ (S) (SI (>>= (<<·>> (·>> object S) O) (! ASSERT)))))))

(define-transitive-verb loves love*)
(define-transitive-verb owns own*)
(define-transitive-verb fascinates fascinate*)
(define-transitive-verb found find*)
(define-transitive-verb beats beat*)
(define-transitive-verb likes like*)
(define-transitive-verb treats-well treat-well*)

;; not-the-case : S → S
(define-checked-term not-the-case
  (λ (A) (d¬ A)))

;; and-sent : S → S
;; This entry was called simply 'and in the dissertation. We call it
;; 'and-sent here so as not to shadow Racket's 'and operator.
(define-checked-term and-sent
  (λ (A) (λ (B) (d∧ A B))))

;; if-then : S → S → S
(define-checked-term if-then
  (λ (A) (λ (B) (d→ A B))))

;; either-or : S → S → S
(define-checked-term either-or
  (λ (A) (λ (B) (d∨ A B))))

;; dot : D → S → D
;; Simply called '. in the dissertation.
(define-checked-term dot
  (λ (D) (λ (S) (>>= D (λ (_) S)))))

;; nil-disc : D
;; The empty discourse. In the dissertation, it is called 'nil. Here we
;; avoid this name because it is already used for the empty context.
(define-checked-term nil-disc
  (η ★))

;; The following entries describe the presupposition triggers. They are
;; based on the extension to the base grammar proposed in Section 8.6.2.

;; the : N → NP
(define-checked-term the
  (λ (N) (>>= (packageProperty (λ (x) (PUSH x (λ (_) (N x))))) (λ (N_)
         (! PRESUPPOSE N_)))))

;; poss : NP → N → NP
(define-checked-term poss
  (λ (X) (λ (N) (>>= X (λ (x)
                (>>= (packageProperty (λ (y) (PUSH y (λ (_)
                                             (ASSERT ((own* x) y) (λ (_)
                                             (N y))))))) (λ (N_)
                (! PRESUPPOSE N_))))))))

;; relational-noun : NP → NP
(define-syntax-rule (define-relational-noun abstract object)
  (define-checked-term abstract
    (λ (X) (>>= X (λ (x)
           (! PRESUPPOSE (λ (y) (! ASSERT ((object y) x)))))))))

(define-relational-noun children-of children*)
(define-relational-noun best-friend best-friend*)
(define-relational-noun mother mother*)

;; proper-noun : NP
(define-syntax-rule (define-proper-noun abstract object)
  (define-checked-term abstract
    (! PRESUPPOSE (λ (x) (! ASSERT (object x))))))

(define-proper-noun John John*)
(define-proper-noun Jones Jones*)
(define-proper-noun Bill Bill*)
(define-proper-noun Mary Mary*)
(define-proper-noun Sarah Sarah*)
(define-proper-noun Ulysses Ulysses*)
(define-proper-noun Socrates Socrates*)

;; who_r : (NP → S) → N → N
(define-checked-term who_r
  (λ (k) (λ (n) (λ (x) (d∧ (n x) (k (η x)))))))

;; who_s : (NP → S) → NP → NP
(define-checked-term who_s
  (λ (C_) (λ (X) (>>= X (λ (x)
                 (>>= (asImplicature (C_ (η x))) (λ (_)
                 (η x))))))))

;; appos : NP → NP → NP
(define-checked-term appos
  (λ (Y) (λ (X) (>>= X (λ (x)
                (>>= (asImplicature (>>= (<<=>> (η x) Y) (! ASSERT))) (λ (_)
                (η x))))))))

;; me : NP
(define-checked-term me
  (! SPEAKER ★))

;; said_is : S → NP → S
(define-checked-term said_is
  (λ (C_) (λ (S) (SI (>>= (<<·>> (·>> say* S) (dbox C_)) (! ASSERT))))))

;; said_ds : S → NP → S
(define-checked-term said_ds
  (λ (C_) (λ (S) (SI (>>= S (λ (s)
                     (>>= (<<·>> (·>> say* S) ((top s) C_)) (! ASSERT))))))))

;; owner-of : NP → N
(define-checked-term owner-of
  (λ (Y) (λ (x) (>>= (·>> (own* x) Y) (! ASSERT)))))

;; in-situ : QNP → NP
(define-checked-term in-situ
  (λ (Q) (>>= Q (λ (X) X))))

;; QR : QNP → (NP → S) → S
(define-checked-term QR
  (λ (Q) (λ (K) (>>= Q K))))

;; The following is a helper combinator for the lexical entry of
;; quantifiers.  (trace x) is a term that evaluates to x but also
;; introduces x to the context.
(define-checked-term trace
  (λ (x) (PUSH x (λ (_) (η x)))))

;; every : N → QNP
(define-checked-term every
  (λ (N) (SCOPE (λ (k) (d∀ (λ (x) (d→ (SI (N x)) (k x)))))
                (λ (x) (η (trace x))))))

;; everyone : QNP
(define-checked-term everyone
  (SCOPE (λ (k) (d∀ k))
         (λ (x) (η (trace x)))))

;; indef_ : N → QNP
;; In the dissertation, this lexical item is called a'.
(define-checked-term indef_
  (λ (N) (SCOPE (λ (k) (d∃ (λ (x) (d∧ (SI (N x)) (k x)))))
                (λ (x) (η (trace x))))))

;; someone : QNP
(define-checked-term someone
  (SCOPE (λ (k) (d∃ k))
         (λ (x) (η (trace x)))))

;; We also add some adjectives and copulas to the grammar to be able to
;; cover the examples seen in Chapter 7.

;; adjective : ADJ
(define-syntax-rule (define-adjective abstract object)
  (define-checked-term abstract object))

(define-adjective angry angry*)
(define-adjective frightened frightened*)
(define-adjective cheap cheap*)
(define-adjective mortal mortal*)

;; get : ADJ → NP → S
(define-checked-term get
  (λ (a) (λ (X) (>>= X (λ (x) (! ASSERT (a x)))))))

;; is : ADJ → NP → S
(define-checked-term is
  (λ (a) (λ (X) (>>= X (λ (x) (! ASSERT (a x)))))))

;; is-a : N → NP → S
(define-checked-term is-a
  (λ (N) (λ (X) (>>= X N))))






;; Examples
;; ========
;; 
;; We end this program with example abstract terms that can be
;; evaluated. The examples are taken from the dissertation and can
;; therefore be used to verify the calculations that are done "on paper" in
;; the dissertation.

;; Every man is mortal. Socrates is a man. (Section 5.1)
;; (compute-truth-conditions example-socrates-hypotheses)
(define-checked-term example-socrates-hypotheses
  (♭ ((top s) ((dot ((dot nil-disc)
                          ((is mortal) (in-situ (every man)))))
                          ((is-a man) Socrates)))))

;; Socrates is mortal. (Section 5.1)
;; (compute-truth-conditions example-socrates-conclusion)
(define-checked-term example-socrates-conclusion
  (♭ ((top s) ((is mortal) Socrates))))

;; Every man loves a unicorn. (Subsection 5.2.3)
;; (compute-truth-conditions (term example-montague-subject-wide))
;; '(∀ (x1) ((man* x1) ⇒ (∃ (x3) ((unicorn* x3) ∧ (love* x1 x3)))))
(define-checked-term example-montague-subject-wide
  (♭ ((top s) ((QR (every man)) (λ (x)
                 ((QR (indef_ unicorn)) (λ (y) ((loves y) x))))))))

;; Every man loves a unicorn. (Subsection 5.2.3)
;; (compute-truth-conditions (term example-montague-object-wide))
(define-checked-term example-montague-object-wide
  (♭ ((top s) ((QR (indef_ unicorn)) (λ (y)
                 ((QR (every man)) (λ (x) ((loves y) x))))))))

;; Jones owns Ulysses. It fascinates him. (Section 5.3)
;; (compute-truth-conditions (term example-jones-ulysses))
(define-checked-term example-jones-ulysses
  (♭ ((top s) ((dot ((dot nil-disc)
                          ((owns Ulysses) Jones)))
                          ((fascinates he) it)))))

;; Jones owns a Porsche. It fascinates him. (Section 5.3, Section 7.1)
;; (compute-truth-conditions (term example-jones-porsche))
(define-checked-term example-jones-porsche
  (♭ ((top s) ((dot ((dot nil-disc)
                          ((owns (indef Porsche)) Jones)))
                          ((fascinates he) it)))))

;; Every farmer who owns a donkey beats it. (Section 5.3)
;; (compute-truth-conditions (term example-donkey-relative))
(define-checked-term example-donkey-relative
  (♭ ((top s) ((beats it)
               (in-situ (every ((who_r (owns (indef donkey))) farmer)))))))

;; If a farmer owns a donkey, he beats it. (Section 5.3)
;; (compute-truth-conditions (term example-donkey-conditional))
(define-checked-term example-donkey-conditional
  (♭ ((top s) ((if-then ((owns (indef donkey)) (indef farmer)))
                        ((beats it) he)))))

;; John loves Mary. (Section 6.2)
;; (compute-truth-conditions (term example-basic))
(define-checked-term example-basic
  (♭ ((top s) ((loves Mary) John))))

;; John loves me. (Section 6.2)
;; (compute-truth-conditions (term example-deixis))
(define-checked-term example-deixis
  (♭ ((top s) ((loves me) John))))

;; John said Mary loves me. (Subsection 6.2.1)
;; (compute-truth-conditions (term example-indirect-speech))
(define-checked-term example-indirect-speech
  (♭ ((top s) ((said_is ((loves me) Mary)) John))))

;; John said "Mary loves me". (Subsection 6.2.1)
;; (compute-truth-conditions (term example-indirect-speech))
(define-checked-term example-direct-speech
  (♭ ((top s) ((said_ds ((loves me) Mary)) John))))

;; Either John loves Sarah, or Mary, John's best friend, loves John. (Section 6.3)
;; (compute-truth-conditions (term example-either-ci-or))
(define-checked-term example-either-ci-or
  ((top s) ((either-or ((loves Sarah) John))
                       ((loves John) ((appos Mary) (best-friend John))))))

;; If it is not the case that John, whom Sarah loves, loves Sarah,
;; then Mary loves John. (Section 6.3)
;; (compute-truth-conditions (term example-if-not-ci-then))
(define-checked-term example-if-not-ci-then
  ((top s) ((if-then (not-the-case ((loves Sarah)
                                    ((who_s (λ (x) ((loves x) Sarah)))
                                     John))))
                     ((loves John) Mary))))

;; Every man loves a woman. (Subsection 6.4.1)
;; (compute-truth-conditions (term example-two-quantifiers-1))
(define-checked-term example-two-quantifiers-1
  (♭ ((top s) ((loves (in-situ (indef_ woman))) (in-situ (every man))))))

;; Every man loves a woman. (Subsection 6.4.1)
;; (compute-truth-conditions (term example-two-quantifiers-2))
(define-checked-term example-two-quantifiers-2
  (♭ ((top s) ((QR (indef_ woman)) (λ (y) ((loves y) (in-situ (every man))))))))

;; Every owner of a siamese cat loves a therapist. (Subsection 6.4.1)
;; (compute-truth-conditions (term example-three-quantifiers-1))
(define-checked-term example-three-quantifiers-1
  (♭ ((top s) ((loves (in-situ (indef_ therapist)))
               (in-situ (every (owner-of (in-situ (indef_ siamese-cat)))))))))

;; Every owner of a siamese cat loves a therapist. (Subsection 6.4.1)
;; (compute-truth-conditions (term example-three-quantifiers-2))
(define-checked-term example-three-quantifiers-2
  (♭ ((top s) ((QR (indef_ siamese-cat)) (λ (y)
                 ((loves (in-situ (indef_ therapist)))
                         (in-situ (every (owner-of y)))))))))

;; Every owner of a siamese cat loves a therapist. (Subsection 6.4.1)
;; (compute-truth-conditions (term example-three-quantifiers-3))
(define-checked-term example-three-quantifiers-3
  (♭ ((top s) ((QR (indef_ therapist)) (λ (z)
         ((loves z)
          (in-situ (every (owner-of (in-situ (indef_ siamese-cat)))))))))))

;; Every owner of a siamese cat loves a therapist. (Subsection 6.4.1)
;; (compute-truth-conditions (term example-three-quantifiers-4))
(define-checked-term example-three-quantifiers-4
  (♭ ((top s) ((QR (indef_ siamese-cat)) (λ (y)
                 ((QR (indef_ therapist)) (λ (z)
                   ((loves z) (in-situ (every (owner-of y)))))))))))

;; Every owner of a siamese cat loves a therapist. (Subsection 6.4.1)
;; (compute-truth-conditions (term example-three-quantifiers-5))
(define-checked-term example-three-quantifiers-5
  (♭ ((top s) ((QR (indef_ therapist)) (λ (z)
                 ((QR (indef_ siamese-cat)) (λ (y)
                   ((loves z) (in-situ (every (owner-of y)))))))))))

;; John loves a man. (Subsection 6.4.2)
;; (compute-truh-conditions (term example-john-man))
(define-checked-term example-john-man
  (♭ ((top s) ((loves (in-situ (indef_ man))) John))))

;; A man owns a Porsche. It fascinates him. (Subsection 7.2.1)
;; (compute-truth-conditions (term example-man-porsche))
(define-checked-term example-man-porsche
  (♭ ((top s) ((dot ((dot nil-disc)
                          ((owns (indef Porsche)) (indef man))))
                          ((fascinate he) it)))))

;; It is not the case that Jones owns a Porsche. He owns a Mercedes. (Section 7.3)
;; (compute-truth-conditions (term example-jones-mercedes))
(define-checked-term example-jones-mercedes
  ((top s) ((dot ((dot nil-disc)
                       (not-the-case ((owns (indef Porsche)) Jones))))
                       ((owns (indef Mercedes)) he))))

;; He loves John's vehicle. (Section 7.3)
;; (compute-truth-conditions (term example-presupposition-crossover))
(define-checked-term example-presupposition-crossover
  (♭ ((top s) ((loves ((poss John) vehicle)) he))))

;; It is not the case that John likes his vehicle. (Subsection 7.3.1)
;; (compute-truth-conditions (term example-not-his-vehicle))
(define-checked-term example-not-his-vehicle
  ((top s) (not-the-case ((likes ((poss he) vehicle)) John))))

;; If John owns a vehicle, then his vehicle is cheap. (Subsection 7.3.3)
;; (compute-truth-conditions (term example-his-vehicle-cheap))
(define-checked-term example-his-vehicle-cheap
  ((top s) ((if-then ((owns (indef vehicle)) John))
                     ((is cheap) ((poss he) vehicle)))))

;; If a man gets angry, his children get frightened. (Subsection 7.3.4)
;; (compute-truth-conditions (term example-frightened))
(define-checked-term example-frightened
  ((top s) ((if-then ((get angry) (indef man)))
                     ((get frightened) (children-of he)))))

;; His mother likes every man. (Subsection 8.5.1)
;; (compute-truth-conditions example-crossover)
(define-checked-term example-crossover
  ((top s) ((QR (every man)) (λ (y) ((likes y) (mother he))))))

;; He likes every man. (Subsection 8.5.1)
;; (compute-truth-conditions example-primary-crossover)
(define-checked-term example-primary-crossover
  (♭ ((top s) ((QR (every man)) (λ (y) ((likes y) he))))))

;; He likes every man's mother. (Subsection 8.5.1)
;; (compute-truth-conditions example-secondary-crossover)
(define-checked-term example-secondary-crossover
  ((top s) ((QR (every man)) (λ (y) ((likes (mother y)) he)))))

;; It loves every owner of a dog. (Subsection 8.5.1)
;; (compute-truth-conditions example-bad-crossover)
(define-checked-term example-bad-crossover
  (♭ ((top s) ((QR (every (owner-of (indef dog)))) (λ (y) ((loves y) it))))))

;; The man who owns a dog loves it. (Subsection 8.6.2)
;; (compute-truth-conditions (term example-presupposition-binding-1))
(define-checked-term example-presupposition-binding-1
  ((top s) ((loves it) (the ((who_r (owns (indef dog))) man)))))

;; The man who loves his dog treats it well. (Subsection 8.6.2)
;; (compute-truth-conditions (term example-presupposition-binding-2))
(define-checked-term example-presupposition-binding-2
  ((top s) ((treats-well it) (the ((who_r (loves ((poss he) dog))) man)))))

;; My best friend, who owns a dog, said it loves everyone.
;; (Section 8.7, Appendix B)
;; (compute-truth-conditions (term example-final))
;; '(∃ (x8) ((best-friend* x8 s) ∧
;;  (∃ (x1) ((dog* x1) ∧ ((own* x8 x1) ∧
;;          (say* x8 (∀ (x6) (love* x1 x6)))))))))
(define-checked-term example-final
  (♭ ((top s) ((said_is ((loves (in-situ everyone)) it))
               ((who_s (owns (indef dog))) (best-friend me))))))
