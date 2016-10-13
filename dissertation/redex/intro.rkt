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
  ...)

;; (free-in x e) is true iff x occurs free in e
(define-metafunction BANANA+SPA
  free-in : x e -> #t or #f
  ...)

;; (subst e x e_new) is the result of substituting e_new for all the free
;; occurrences of x in e (i.e. e[x := e_new])
(define-metafunction BANANA+SPA
  subst : e x e -> e
  ...)
