#lang racket
(require redex)

(define-language EH
  (e ::= (e e)
         (λ (x t) e)
         x
         c
         (pure e)
         (op e (λ (x t) e))
         (e >>= (λ (x t) e))
         (handler (op_!_ e) ... (pure e)))
  (t ::= (t -> t)
         v
         (F t))
  (x ::= variable-not-otherwise-mentioned)
  (c ::= variable-not-otherwise-mentioned)
  (v ::= variable-not-otherwise-mentioned)
  (op ::= variable-not-otherwise-mentioned)
  (G ::= * (x : t G))
  (C ::= * (c : t C))
  (E ::= * (op : (t -> t) E))
  (context ::= G C E)
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
  #:mode (env I I O)
  #:contract (env context key t)
  
  [-------------------
   (env (key : t context) key t)]
  
  [(env context key_1 t_1)
   (side-condition (different key_1 key_2))
   ------------------------------------
   (env (key_2 : t_2 context) key_1 t_1)])

(define-judgment-form
  EH
  #:mode (types I I I I O)
  #:contract (types G C E e t)
  
  [(types G C E e_1 (t_2 -> t_3))
   (types G C E e_2 t_2)
   ------------------------------
   (types G C E (e_1 e_2) t_3)]
  
  [(types (x : t_1 G) C E e t_2)
   ------------------------------------------
   (types G C E (λ (x t_1) e) (t_1 -> t_2))]
  
  [-------------------------
   (types (x : t G) C E x t)]
  
  [(env G x t)
   -----------------
   (types G C E x t)]
  
  [(env C c t)
   -----------------
   (types G C E c t)]
  
  [(env E op (t_1 -> t_2))
   (types G C E e_arg t_1)
   (types G C E e_k (t_2 -> (F (t_3))))
   ---------------------------------
   (types G C E (op e_arg e_k) (F t_3))]
  
  [(types G C E e t)
   ----------------------------
   (types G C E (pure e) (F t))]
  
  [(types G C E e_1 (F t_1))
   (types G C E e_2 (t_1 -> (F t_2)))
   -----------------------------------
   (types G C E (e_1 >>= e_2) (F t_2))]
  
  [(env E op (t_arg -> t_res)) ...
   (types G C E e_h (t_arg -> ((t_res -> (F t_out_h)) -> (F t_out_h)))) ...
   (types G C E e_p (t_in -> (F t_out)))
   (side-condition (all-match t_out (t_out_h ...)))
   -------------------------------------------------------------------
   (types G C E (handler (op e_h) ... (pure e_p)) ((F t_in) -> (F t_out)))])


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
  [(free-in x (e_m >>= e_k))
   ,(or (term (free-in x e_m)) (term (free-in x e_k)))]
  [(free-in x (handler (op_i e_i) ... (pure e_p)))
   ,(or (ormap identity (term ((free-in x e_i) ...))) (term (free-in x e_p)))])

(define-metafunction EH
  subst : x e e -> e
  [(subst x e_new (e_f e_a))
   ((subst x e_new e_f) (subst x e_new e_a))]
  [(subst x e_new (λ (x t) e_body))
   (λ (x t) e_body)]
  [(subst x e_new (λ (x_arg t) e_body))
   ,(if (term (free-in x_arg e_new))
      (let ([x_f (variable-not-in (term (e_new e_body)) (term x_arg))])
        (term (λ (,x_f t) (subst x e_new (subst x_arg ,x_f e_body)))))
      (term (λ (x_arg t) (subst x e_new e_body))))]
  [(subst x e_new x)
   e_new]
  [(subst x e_new x_different)
   x_different]
  [(subst x e_new c)
   c]
  [(subst x e_new (pure e))
   (pure (subst x e_new e))]
  [(subst x e_new (op e_arg e_k))
   (op (subst x e_new e_arg) (subst x e_new e_k))]
  [(subst x e_new (e_m >>= e_k))
   ((subst x e_new e_m) >>= (subst x e_new e_k))]
  [(subst x e_new (handler (op_i e_i) ... (pure e_p)))
   (handler (op_i (subst x e_new e_i)) ... (pure (subst x e_new e_p)))])

(define eval
  (compatible-closure 
   (reduction-relation
    EH
    #:domain e
    (--> ((λ (x t) e_1) e_2)
         (subst x e_2 e_1)
         "beta")
    (--> ((pure e_x) >>= e_k)
         (e_k e_x)
         "pure->>=")
    (--> ((op e_arg (λ (x t) e_1)) >>= e_k2)
         (op e_arg (λ (x_f t) ((subst x x_f e_1) >>= e_k2)))
         (fresh x_f)
         "op->>=")
    (--> ((handler (op_i e_i) ... (pure e_p)) (pure e_v))
         (e_p e_v)
         "handle-pure")
    (--> ((handler (op_1 e_1) ... (op_2 e_2) (op_3 e_3) ... (pure e_p)) (op_2 e_arg (λ (x t) e_m)))
         ((e_2 e_arg) (λ (x_f t) ((handler (op_1 e_1) ... (op_2 e_2) (op_3 e_3) ... (pure e_p)) (subst x x_f e_m))))
         (fresh x_f)
         "handle-op")
    (--> ((handler (op_i e_i) ... (pure e_p)) (op e_arg (λ (x t) e_m)))
         (op e_arg (λ (x_f t) ((handler (op_i e_i)... (pure e_p)) (subst x x_f e_m))))
         (side-condition (term (no-match op (op_i ...))))
         (fresh x_f)
         "handle-missing-op"))
   EH
   e))


(define std-consts
  (term (unit : u (
         and : (o -> (o -> o)) (
         or : (o -> (o -> o)) (
         imp : (o -> (o -> o)) (
         not : (o -> o) (
         ex : ((i -> o) -> o) (
         all : ((i -> o) -> o) (
         sel : (c -> i) (
         nil : c (
         add : (i -> (c -> c)) (
         love : (i -> (i -> o)) (
         john : i (
         mary : i (
         sleep : (i -> o)
         *))))))))))))))))

(define std-effects
  (term (GET : (u -> c) (
         FRESH : (u -> i) (
         ASSERT : (o -> u) (
         SCOPE-OVER : (((i -> (F o)) -> (F o)) -> i)
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
                                    ((k e) >>=
                                     (λ (f (c -> (F o))) (f e))))))))
          (ASSERT (λ (p o) (λ (k (u -> (F (c -> (F o)))))
                    ((k unit) >>=
                      (λ (Q (c -> (F o)))
                        (pure (λ (e c)
                                ((Q e) >>=
                                 (λ (q o) (pure ((and p) q)))))))))))
          (pure (λ (x o) (pure (λ (e c) (pure x))))))))

(check-type drs-handler (term ((F o) -> (F (c -> (F o))))))

(define drs
  (term (λ (e c)
          (λ (P (F o))
            ((,drs-handler P) >>=
             (λ (f (c -> (F o))) (f e)))))))

(check-type drs (term (c -> ((F o) -> (F o)))))

(define top-drs
  (term (,drs nil)))

(check-type top-drs (term ((F o) -> (F o))))

(define tensed-clause-handler
  (term (handler
          (SCOPE-OVER (λ (c ((i -> (F o)) -> (F o)))
                        (λ (k (i -> (F o)))
                          (c k))))
          (pure (λ (x o) (pure x))))))

(check-type tensed-clause-handler (term ((F o) -> (F o))))



(define-judgment-form EH
  #:mode (alpha-equiv I I)
  
  [---------------------
   (alpha-equiv any any)]
  
  [(alpha-equiv any_1 any_2) ...
   -------------------------------------
   (alpha-equiv (any_1 ...) (any_2 ...))]

  [(where x_3 ,(variable-not-in (term (e_1 e_2)) (string->uninterned-symbol "x")))
   (alpha-equiv (subst x_1 x_3 e_1) (subst x_2 x_3 e_2))
   -------------------------------------------------------------------------------
   (alpha-equiv (λ (x_1 t) e_1) (λ (x_2 t) e_2))])

(define (alpha-equiv? e1 e2)
  (not (null? (judgment-holds (alpha-equiv ,e1 ,e2) #t))))

(define (normal? e)
  (null? (apply-reduction-relation eval e)))

(define checked 0)
(define cover (make-coverage eval))

(define (normalizes? e)
  (print e)
  (newline)
  (let* ([normal-forms (apply-reduction-relation* eval e)]
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


'['subst (λ (lws) (list (list-ref lws 4) "[" (list-ref lws 2) "/" (list-ref lws 3) "]"))]

(with-compound-rewriters (['no-match (λ (lws) (list (list-ref lws 2) " ∉ " (list-ref lws 3)))]
                          ['types (λ (lws) (list (list-ref lws 2) " ⊢ " (list-ref lws 5) " : " (list-ref lws 6)))]
                          ['env (λ (lws) (list (list-ref lws 3) " : " (list-ref lws 4) " ∈ " (list-ref lws 2)))])
  (begin (render-reduction-relation eval)
         (render-judgment-form types)))

