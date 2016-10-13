;; Grammar
;; =======
;;
;; What follows are lambda-banana terms which are the interpretations of
;; the lexical items that make up our grammar. This grammar combines all of
;; the phenomena discussed in Chapter 8 of the dissertation. In this edited
;; version, we only include the entries which feature in the example that
;; we study in Appendix B. For the complete grammar, see
;; https://github.com/jirkamarsik/ling-eff/blob/master/redex/untyped-bananas.rkt

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

(define-common-noun dog dog*)

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

;; relational-noun : NP → NP
(define-syntax-rule (define-relational-noun abstract object)
  (define-checked-term abstract
    (λ (X) (>>= X (λ (x)
           (! PRESUPPOSE (λ (y) (! ASSERT ((object y) x)))))))))

(define-relational-noun best-friend best-friend*)

;; who_s : (NP → S) → NP → NP
(define-checked-term who_s
  (λ (C_) (λ (X) (>>= X (λ (x)
                 (>>= (asImplicature (C_ (η x))) (λ (_)
                 (η x))))))))

;; me : NP
(define-checked-term me
  (! SPEAKER ★))

;; said_is : S → NP → S
(define-checked-term said_is
  (λ (C_) (λ (S) (SI (>>= (<<·>> (·>> say* S) (dbox C_)) (! ASSERT))))))

;; in-situ : QNP → NP
(define-checked-term in-situ
  (λ (Q) (>>= Q (λ (X) X))))

;; The following is a helper combinator for the lexical entry of
;; quantifiers.  (trace x) is a term that evaluates to x but also
;; introduces x to the context.
(define-checked-term trace
  (λ (x) (PUSH x (λ (_) (η x)))))

;; everyone : QNP
(define-checked-term everyone
  (SCOPE (λ (k) (d∀ k))
         (λ (x) (η (trace x)))))



;; Examples
;; ========
;; 
;; We end this program with example abstract terms that can be
;; evaluated. The examples are taken from the dissertation and can
;; therefore be used to verify the calculations that are done "on paper" in
;; the dissertation. In this edited version, we include only
;; the example from Appendix B.

;; My best friend, who owns a dog, said it loves everyone.
;; (Section 8.7, Appendix B)
;; (compute-truth-conditions (term example-final))
;; '(∃ (x8) ((best-friend* x8 s) ∧
;;  (∃ (x1) ((dog* x1) ∧ ((own* x8 x1) ∧
;;          (say* x8 (∀ (x6) (love* x1 x6)))))))))
(define-checked-term example-final
  (♭ ((top s) ((said_is ((loves (in-situ everyone)) it))
               ((who_s (owns (indef dog))) (best-friend me))))))
