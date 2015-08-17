#lang racket
(require redex)

(define-language EH
  (e ::= (e e)
         (λ (x t) e)
         x
         c
         (pure e)
         (op e (λ (x t) e))
         (handler (op e) ... (pure e))
         (C e))
  (t ::= (t -> t)
         v
         (F t))
  (x ::= variable-not-otherwise-mentioned)
  (c ::= variable-not-otherwise-mentioned)
  (v ::= variable-not-otherwise-mentioned)
  (op ::= variable-not-otherwise-mentioned)
  (G ::= * (x : t G))
  (S ::= * (c : t S))
  (E ::= * (op : (t -> t) E))
  (context ::= G S E)
  (key ::= x c op))

(define-metafunction EH
  different : any any -> #t or #f
  [(different any_1 any_1) #f]
  [(different any_1 any_2) #t])

(define-metafunction EH
  all-match : any (any ...) -> #t or #f
  [(all-match any_1 (any_1 any_more ...))
   (all-match any_1 (any_more ...))]
  [(all-match any_1 (any_2 any_more ...))
   #f]
  [(all-match any_1 ())
   #t])

(define-metafunction EH
  no-match : any (any ...) -> #t or #f
  [(no-match any_1 (any_1 any_more ...))
   #f]
  [(no-match any_1 (any_2 any_more ...))
   (no-match any_1 (any_more ...))]
  [(no-match any_1 ())
   #t])

(define-judgment-form
  EH
  #:mode (env I O I)
  #:contract (env key t context)
  
  [-----------------------------
   (env key t (key : t context))]
  
  [(env key_1 t_1 context)
   (side-condition (different key_1 key_2))
   ----------------------------------------
   (env key_1 t_1 (key_2 : t_2 context))])

(define-judgment-form
  EH
  #:mode (types I I I I O)
  #:contract (types G S E e t)
  
  [(types G S E e_1 (t_2 -> t_3))
   (types G S E e_2 t_2)
   ------------------------------ "app"
   (types G S E (e_1 e_2) t_3)]
  
  [(types (x : t_1 G) S E e t_2)
   ---------------------------------------- "abs"
   (types G S E (λ (x t_1) e) (t_1 -> t_2))]
  
  [(env x t G)
   ----------------- "var"
   (types G S E x t)]
  
  [(env c t S)
   ----------------- "const"
   (types G S E c t)]
  
  [(types G S E e t)
   ---------------------------- "pure"
   (types G S E (pure e) (F t))]
  
  [(env op (t_1 -> t_2) E)
   (types G S E e_arg t_1)
   (types G S E e_k (t_2 -> (F t_3)))
   ------------------------------------ "op"
   (types G S E (op e_arg e_k) (F t_3))]
  
  [(env op (t_arg -> t_res) E) ...
   (types G S E e_h (t_arg -> ((t_res -> (F t_out_h)) -> (F t_out_h)))) ...
   (types G S E e_p (t_in -> (F t_out)))
   (side-condition (all-match t_out (t_out_h ...)))
   ------------------------------------------------------------------------ "handler"
   (types G S E (handler (op e_h) ... (pure e_p)) ((F t_in) -> (F t_out)))]
  
  [(types G S E e (t_1 -> (F t_2)))
   ------------------------------------ "𝓒"
   (types G S E (C e) (F (t_1 -> t_2)))])


(define-metafunction EH
  free-in : x e -> #t or #f
  [(free-in x (e_f e_a))
   ,(or (term (free-in x e_f)) (term (free-in x e_a)))]
  [(free-in x (λ (x t) e))
   #f]
  [(free-in x (λ (x_different t) e))
   (free-in x e)]
  [(free-in x x)
   #t]
  [(free-in x x_different)
   #f]
  [(free-in x c)
   #f]
  [(free-in x (pure e))
   (free-in x e)]
  [(free-in x (op e_arg e_k))
   ,(or (term (free-in x e_arg)) (term (free-in x e_k)))]
  [(free-in x (handler (op_i e_i) ... (pure e_p)))
   ,(or (ormap identity (term ((free-in x e_i) ...))) (term (free-in x e_p)))]
  [(free-in x (C e))
   (free-in x e)])

(define-metafunction EH
  subst : e x e -> e
  [(subst (e_f e_a) x e_new)
   ((subst e_f x e_new) (subst e_a x e_new))]
  [(subst (λ (x t) e_body) x e_new)
   (λ (x t) e_body)]
  [(subst (λ (x_arg t) e_body) x e_new)
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
  [(subst (pure e) x e_new)
   (pure (subst e x e_new))]
  [(subst (op e_arg e_k) x e_new)
   (op (subst e_arg x e_new) (subst e_k x e_new))]
  [(subst (handler (op_i e_i) ... (pure e_p)) x e_new)
   (handler (op_i (subst e_i x e_new)) ... (pure (subst e_p x e_new)))]
  [(subst (C e) x e_new)
   (C (subst e x e_new))])

(define eval
  (compatible-closure 
   (reduction-relation
    EH
    #:domain e
    (--> ((λ (x t) e_1) e_2)
         (subst e_1 x e_2)
         "beta")
    (--> (C (λ (x t) (pure e)))
         (pure (λ (x t) e))
         "C-pure")
    (--> (C (λ (x t) (op e_a (λ (x_k t_k) e_k))))
         (op e_a (λ (x_k t_k) (C (λ (x t) e_k))))
         (side-condition (not (term (free-in x e_a))))
         "C-op")
    (--> ((handler (op_i e_i) ... (pure e_p)) (pure e_v))
         (e_p e_v)
         "handle-pure")
    (--> ((handler (op_1 e_1) ... (op_2 e_2) (op_3 e_3) ... (pure e_p)) (op_2 e_arg (λ (x t) e_m)))
         ((e_2 e_arg) (λ (x_f t) ((handler (op_1 e_1) ... (op_2 e_2) (op_3 e_3) ... (pure e_p)) (subst e_m x x_f))))
         (side-condition (term (no-match op_2 (op_1 ...))))
         (fresh x_f)
         "handle-op")
    (--> ((handler (op_i e_i) ... (pure e_p)) (op e_arg (λ (x t) e_m)))
         (op e_arg (λ (x_f t) ((handler (op_i e_i) ... (pure e_p)) (subst e_m x x_f))))
         (side-condition (term (no-match op (op_i ...))))
         (fresh x_f)
         "handle-missing-op"))
   EH
   e))

(define-metafunction EH
  >>= : e e -> e
  [(>>= e_m e_k)
   ((handler (pure e_k)) e_m)])



;; Some bigger example terms

(define std-consts
  (term (unit : u (
         and : (o -> (o -> o)) (
         not : (o -> o) (
         ex : ((i -> o) -> o) (
         sel : (c -> i) (
         nil : c (
         cons : (i -> (c -> c)) (
         cat : (c -> (c -> c)) (
         eq_i : (i -> (i -> o)) (
         man : (i -> o) (
         woman : (i -> o) (
         love : (i -> (i -> o)) (
         know : (i -> (i -> o)) (
         say : (i -> (o -> o)) (
         john : i (
         mary : i (
         alice : i
         *)))))))))))))))))))

(define std-effects
  (term (GET : (u -> c) (
         FRESH : (u -> i) (
         ASSERT : (o -> u) (
         SCOPE : (((i -> (F o)) -> (F o)) -> i)
         *))))))

(define (check-type exp type)
  (test-equal (judgment-holds
               (types * ,std-consts ,std-effects ,exp t)
               t)
              (list type)))

(define drs-handler
  (term (handler
          (GET (λ (u u) (λ (k (c -> (F (c -> (F o)))))
                            (pure (λ (e c)
                                    (GET unit (λ (e_ c) (>>= (k ((cat e) e_))
                                                             (λ (f (c -> (F o))) (f e))))))))))
          (FRESH (λ (u u) (λ (k (i -> (F (c -> (F o)))))
                            (pure (λ (e c)
                                    (>>= (C (λ (x i) (>>= (k x)
                                                          (λ (f (c -> (F o)))
                                                            (f ((cons x) e))))))
                                         (λ (pred (i -> o)) (pure (ex pred)))))))))
          (ASSERT (λ (p o) (λ (k (u -> (F (c -> (F o)))))
                             (pure (λ (e c)
                                     (>>= (k unit)
                                          (λ (f (c -> (F o)))
                                            (>>= (f e)
                                                 (λ (q o) (pure ((and p) q)))))))))))
          (pure (λ (x o) (pure (λ (e c) (pure x))))))))

(check-type drs-handler (term ((F o) -> (F (c -> (F o))))))

(define box
  (term (λ (P (F o))
          (>>= (,drs-handler P)
               (λ (f (c -> (F o))) (f nil))))))

(check-type box (term ((F o) -> (F o))))

(define SI
  (term (handler
          (SCOPE (λ (c ((i -> (F o)) -> (F o)))
                        (λ (k (i -> (F o)))
                          (c k))))
          (pure (λ (x o) (pure x))))))

(check-type SI (term ((F o) -> (F o))))



;; Generating counter-examples to normalization

(define-judgment-form EH
  #:mode (alpha-equiv I I)
  
  [---------------------
   (alpha-equiv any any)]
  
  [(alpha-equiv any_1 any_2) ...
   -------------------------------------
   (alpha-equiv (any_1 ...) (any_2 ...))]

  [(where x_3 ,(variable-not-in (term (e_1 e_2)) (string->uninterned-symbol "x")))
   (alpha-equiv (subst e_1 x_1 x_3) (subst e_2 x_2 x_3))
   -------------------------------------------------------------------------------
   (alpha-equiv (λ (x_1 t) e_1) (λ (x_2 t) e_2))])

(define (alpha-equiv? e1 e2)
  (not (null? (judgment-holds (alpha-equiv ,e1 ,e2) #t))))

(define checked 0)
(define cover (make-coverage eval))

(define (normalizes? e)
  (print e)
  (newline)
  (flush-output)
  (let* ([normal-forms (apply-reduction-relation* eval e #:cache-all? #t)]
         [n (length normal-forms)])
    (set! checked (+ 1 checked))
    (when (= 0 (modulo checked 100))
        (print checked)
        (newline)
        (print e)
        (newline)
        (print (covered-cases cover))
        (newline))
    (if (positive? n)
      (andmap alpha-equiv? (take normal-forms (- n 1)) (drop normal-forms 1))
      #t)))

(define (check-normalization)
  (parameterize ([relation-coverage (list cover)])
    (check-reduction-relation
     eval
     normalizes?)))



;; Typesetting the language definition

(define (render)
  (with-compound-rewriters (['no-match (λ (lws) (list "" (list-ref lws 2) " ∉ " (list-ref lws 3) ""))]
                            ['all-match (λ (lws) (list "" (list-ref lws 2) " = " (list-ref lws 3) ""))]
                            ['subst (λ (lws) (list "" (list-ref lws 2) "[" (list-ref lws 3) "/" (list-ref lws 4) "]"))]
                            ['types (λ (lws) (list "" (list-ref lws 2) ", " (list-ref lws 3) ", " (list-ref lws 4) " ⊢ " (list-ref lws 5) " : " (list-ref lws 6) ""))]
                            ['env (λ (lws) (list "" (list-ref lws 2) " : " (list-ref lws 3) " ∈ " (list-ref lws 4) ""))]
                            ['free-in (λ (lws) (list "" (list-ref lws 2) " ∈ FV(" (list-ref lws 3) ")"))]
                            ['not (λ (lws) (list "¬(" (list-ref lws 2) ")"))])
      (with-atomic-rewriter 't "τ"
      (with-atomic-rewriter '-> "→"
      (with-atomic-rewriter 'F "𝓕"
      (with-atomic-rewriter 'G "Γ"
      (with-atomic-rewriter 'S "Σ"
      (with-atomic-rewriter '* "·"
      (with-atomic-rewriter 'C "𝓒"
        (begin (render-language EH "grammar.ps" #:nts (remove* '(context key) (language-nts EH)))
               (render-judgment-form types "typings.ps")
               (render-reduction-relation eval "reductions.ps")))))))))))


;; Termination counter-example

(define star
  (term (F u)))

(define fstar
  (term (,star -> ,star)))

(define dagger
  (term (λ (y ,star) y)))

(define rec-effect
  (term (REC : (,fstar -> u) *)))

(define roll
  (term (λ (x ,fstar) (REC x (λ (z u) (pure z))))))

(define unroll
  (term (handler (REC (λ (x ,fstar) (λ (k (u -> (F ,fstar))) (pure x))))
                 (pure (λ (x u) (pure ,dagger))))))

(define app
  (term (λ (f ,star) (λ (a ,star) (>>= (,unroll f) (λ (f1 (,star -> ,star)) (f1 a)))))))

(define abs
  roll)

(define delta
  (term (,abs (λ (x ,star) ((,app x) x)))))

(define omega
  (term ((,app ,delta) ,delta)))