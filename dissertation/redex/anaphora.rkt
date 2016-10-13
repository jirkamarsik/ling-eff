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

;; reduce-more extends the reduction relation 'reduce of our calculus. It
;; adds rules that concatenate contexts and look within them for anaphoric
;; antecedents.
(define reduce-more
  (compatible-closure
    (extend-reduction-relation reduce
      BANANA+SPAC ;; BANANA+SPAC extends BANANA+SPA with the gender markers
                  ;; 'masculine, 'feminine and 'neutral
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
           "selP-not-found")) BANANA+SPAC e))
