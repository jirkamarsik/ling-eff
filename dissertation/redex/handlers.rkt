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
   ,(term-let ([x_f1 (variable-not-in (term e_k) 'x)]
               [x_f2 (variable-not-in (term (e_k x_f1)) '_)])
              (term (FRESH e_u (λ (x_f1)
                                 (PUSH x_f1 (λ (x_f2)
                                              (e_k x_f1)))))))])

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

;; We will need to make a nondeterministic choice when trying to accommodate
;; a presupposition at different levels. The choose expression constructor,
;; which corresponds to the + operator in the dissertation (Section 8.2),
;; gives us a convenient syntax for the choice operation AMB : 1 → 2.
(define-metafunction BANANA+SPA
  choose : e e -> e
  [(choose e_1 e_2)
   ,(term-let ([x_f (variable-not-in (term (e_1 e_2)) 'b)])
              (term (AMB ★ (λ (x_f) (ifte x_f e_1 e_2)))))])

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
;; found within the context without having to be accommodated.
(define-checked-term dbox
  (∘ box maybeAccommodate useFind))








;; The next two handlers are the handlers for conventional implicature from
;; Section 8.3.  The asImplicature handler translates ASSERT to IMPLICATE
;; and INTRODUCE (i.e. FRESH and PUSH) to INTRODUCE_I (i.e. FRESH_I and
;; PUSH_I).
(define-checked-term asImplicature
  (handler-η (FRESH (gen FRESH_I))
             (PUSH (gen PUSH_I))
             (ASSERT (gen IMPLICATE))))
;; The withImplicatures handler reintegrates implicatures into the layer of
;; asserted meaning by reversing the translation done by asImplicature.
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
