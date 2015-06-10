#lang racket
(require racket/set racket/match)
(require redex)

(define-language EH
  (e ::= (e e)
         (λ (x : t) e)
         x
         c
         (pure e)
         (e >>= e)
         op
         h
         hole)
  (t ::= (t -> t)
         (F t)
         v)
  (h ::= (handler : (t => t) op-clause ... val-clause))
  (clause ::= op-clause val-clause)
  (op-clause ::= (op x x -> e))
  (val-clause ::= (val x -> e))
  (x ::= variable-not-otherwise-mentioned)
  (c ::= variable-not-otherwise-mentioned)
  (v ::= variable-not-otherwise-mentioned)
  (op ::= variable-not-otherwise-mentioned)
  (G ::= * (x : t G))
  (C ::= * (c : t C))
  (E ::= * (op : (t -> t) E)))

(define-metafunction EH
  [(different x_1 x_1) #f]
  [(different x_1 x_2) #t])

(define-judgment-form
  EH
  #:mode (env I I O)
  
  [-------------------
   (env (x : t G) x t)]
  
  [(env G x_1 t_1)
   (side-condition (different x_1 x_2))
   ------------------------------------
   (env (x_2 : t_2 G) x_1 t_1)])

(define-judgment-form
  EH
  #:mode (clause-types I I I I I I)
  #:contract (clause-types G C E clause t t)
  
  [(types (x : t_in G) C E e (F t_out))
   --------------------------------------------
   (clause-types G C E (val x -> e) t_in t_out)]
  
  [(env E op (t_1 -> t_2))
   (types (x : t_1 (k : (t_2 -> (F t_out)) G)) C E e (F t_out))
   ------------------------------------------------------------
   (clause-types G C E (op x k -> e) t_in t_out)])

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
   (types G C E (λ (x : t_1) e) (t_1 -> t_2))]
  
  [-------------------------
   (types (x : t G) C E x t)]
  
  [(env G x t)
   -----------------
   (types G C E x t)]
  
  [(env C c t)
   -----------------
   (types G C E c t)]
  
  [(env E op (t_1 -> t_2))
   ---------------------------------
   (types G C E op (t_1 -> (F t_2)))]
  
  [(types G C E e t)
   ----------------------------
   (types G C E (pure e) (F t))]
  
  [(types G C E e_1 (F t_1))
   (types G C E e_2 (t_1 -> (F t_2)))
   -----------------------------------
   (types G C E (e_1 >>= e_2) (F t_2))]
  
  [(clause-types G C E clause t_in t_out) ...
   ----------------------------------------------------------------------------
   (types G C E (handler : (t_in => t_out) clause ...) ((F t_in) -> (F t_out)))])



(define (subst/proc x? vars replacements body)
  (define replacements-ht
    (for/fold ([m (hash)])
              ([v (in-list vars)]
               [rep (in-list replacements)])
      (hash-set m v rep)))
  (define replacements-free-vars (for/list ([x (in-set (fvs x? replacements))]) x))
  (define replacements-fresh-vars (variables-not-in (cons vars body) 
                                                    replacements-free-vars))
  (define init-fv-map 
    (for/fold ([m (hash)])
              ([fresh (in-list replacements-fresh-vars)]
               [free (in-list replacements-free-vars)])
      (hash-set m free fresh)))
  (let loop ([body body]
             [fvs-inactive init-fv-map]
             [fvs-active (hash)]
             [replacements replacements-ht])
    (match body
      [`(λ (,xs : ,ts) ... ,body)
       (define-values (new-xs new-inactive new-active new-replacements)
         (adjust-active-inactive xs fvs-inactive fvs-active replacements))
       `(λ ,@(map (λ (x t) `(,x : ,t)) new-xs ts)
          ,(loop body new-inactive new-active new-replacements))]
      [(? x? x)
       (cond
         [(hash-ref fvs-active x #f) => values]
         [(hash-ref replacements x #f) => values]
         [else x])]
      [(? list?)
       (map (λ (x) (loop x fvs-inactive fvs-active replacements))
            body)]
      [_ body])))

(define (adjust-active-inactive xs fvs-inactive fvs-active replacements)
  (let loop ([xs xs]
             [new-xs '()]
             [fvs-inactive fvs-inactive]
             [fvs-active fvs-active]
             [replacements replacements])
    (cond
      [(null? xs)
       (values (reverse new-xs)
               fvs-inactive 
               fvs-active
               replacements)]
      [else
       (define x (car xs))
       (define inactive-var? (hash-has-key? fvs-inactive x))
       (define active-var? (hash-has-key? fvs-active x))
       (define new-x
         (cond
           [inactive-var? (hash-ref fvs-inactive x)]
           [active-var? (hash-ref fvs-active x)]
           [else x]))
       (loop (cdr xs)
             (cons new-x new-xs)
             (if inactive-var?
                 (hash-remove fvs-inactive x)
                 fvs-inactive)
             (if inactive-var?
                 (hash-set fvs-active x (hash-ref fvs-inactive x))
                 fvs-active)
             (if (hash-has-key? replacements x)
                 (hash-remove replacements x)
                 replacements))])))

(define (fvs x? body)
  (let loop ([body body])
    (match body
      [`(λ (,xs ,ts) ... ,body)
       (set-subtract (loop body) (apply set xs))]
      [(? x?)
       (set body)]
      [(? list?)
       (for/fold ([fvs (set)])
                 ([e (in-list body)])
         (set-union fvs (loop e)))]
      [_ (set)])))


(define-metafunction EH
  subst : x v e -> e
  [(subst x v e)
   ,(subst/proc (redex-match EH x) (list (term x)) (list (term v)) (term e))])

(define eval
  (reduction-relation
   EH
   #:domain e
   (==> ((λ (x) e_1) e_2) e_1 "beta")
   with
   [(--> (in-hole e a) (in-hole e b))
    (==> a b)]))


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
         SCOPE_OVER : (((i -> (F o)) -> (F o)) -> i)
         *))))))

(define (check-type exp type)
  (test-equal (judgment-holds
               (types * ,std-consts ,std-effects ,exp t)
               t)
              (list type)))

(define drs-handler
  (term (handler : (o => (c -> (F o)))
          (GET u k -> (pure (λ (e : c)
                              ((k e) >>=
                               (λ (f : (c -> (F o))) (f e))))))
          (ASSERT p k -> ((k unit) >>=
                          (λ (Q : (c -> (F o)))
                            (pure (λ (e : c)
                                    ((Q e) >>=
                                     (λ (q : o) (pure ((and p) q)))))))))
          (val x -> (pure (λ (e : c) (pure x)))))))

(check-type drs-handler (term ((F o) -> (F (c -> (F o))))))

(define drs
  (term (λ (e : c)
          (λ (P : (F o))
            ((,drs-handler P) >>=
             (λ (f : (c -> (F o))) (f e)))))))

(check-type drs (term (c -> ((F o) -> (F o)))))

(define top-drs
  (term (,drs nil)))

(check-type top-drs (term ((F o) -> (F o))))

(define tensed-clause-handler
  (term (handler : (o => o)
          (SCOPE_OVER c k -> (c k))
          (val x -> (pure x)))))

(check-type tensed-clause-handler (term ((F o) -> (F o))))