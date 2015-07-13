#lang racket
(require redex)

;; This semantics comes from the paper
;; _A Natural Semantics for Lazy Evaluation_,
;; by John Launchbury, POPL 1993
;; extended with integers, +, and if0.

(define-language L
  (e ::=
     v
     (e x)
     (let ([x e] ...) e)
     x
     (+ e e)        ;; add addition
     (if0 e e e))   ;; add conditional
  (v ::=            ;; don't use 'z' for values, 
     ;;                because that's confusing
     i              ;; add integer constants
     (λ (x) e))
  
  (i ::= integer)
  (x y z ::= variable-not-otherwise-mentioned)
  
  (Γ Δ Θ ::= · (Γ x ↦ e))

  #:binding-forms
  (let ([x e] ...) e_body #:refers-to (rib x ...))
  (λ (x) e #:refers-to x))

(define-judgment-form L
  #:mode (⇓ I I O O)
  #:contract (⇓ Γ e Δ v)
  
  
  [----------- Value
   (⇓ Γ v Γ v)]
  
  
  [(⇓ Γ e Δ (λ (y) e_*))
   (⇓ Δ (subst e_* y x) Θ v)
   ------------------------- Application
   (⇓ Γ (e x) Θ v)]
  
  
  [(where (Γ x ↦ e) (separate Γ_* x))
   (⇓ Γ e Δ v)
   (where Δ_* (Δ x ↦ v))
   ---------------------------------- Variable
   (⇓ Γ_* x Δ_* v)]
  
  
  [(⇓ (extend Γ (x_i e_i) ...) e Δ v)
   ---------------------------------- Let
   (⇓ Γ (let ([x_i e_i] ...) e) Δ v)]
  
  
  [(⇓ Γ e_1 Θ i_1)
   (⇓ Θ e_2 Δ i_2)
   ---------------------------------------------- Add
   (⇓ Γ (+ e_1 e_2) Δ ,(+ (term i_1) (term i_2)))]
  
  
  [(⇓ Γ e_1 Θ i)
   (⇓ Θ (choose i e_2 e_3) Δ v)
   ---------------------------- If
   (⇓ Γ (if0 e_1 e_2 e_3) Δ v)])

(define-metafunction L
  choose : i e e -> e
  [(choose 0 e_1 e_2) e_1]
  [(choose i e_1 e_2) e_2])

(define-metafunction L
  separate : Γ x -> (Γ x ↦ e) or ⊥
  [(separate · x) ⊥]
  [(separate (Γ x ↦ e) x) (Γ x ↦ e)]
  [(separate (Γ y ↦ e_*) x)
   ((Γ_* y ↦ e_*) x ↦ e)
   (where (Γ_* x ↦ e) (separate Γ x))]
  [(separate (Γ y ↦ e_*) x) ⊥
   (where ⊥ (separate Γ x))])

(define-metafunction L
  extend : Γ (x e) ... -> Γ
  [(extend Γ) Γ]
  [(extend Γ (x e) (x_* e_*) ...)
   (extend (Γ x ↦ e) (x_* e_*) ...)])

(define-metafunction L
  subst : any x any -> any
  [(subst (any_sub ...) x any) ((subst any_sub x any) ...)]
  [(subst x x any) any]
  [(subst any_different x any) any_different])






(define e? (redex-match? L e))
(define v? (redex-match? L v))
(define T-v? (redex-match? L (T v)))


;; run a program to get it's result
(define/contract (run p)
  (-> e? (or/c v? #f))
  (define vs (judgment-holds (⇓ · ,p Δ v) v))
  (cond
    [(pair? vs)
     (unless (= 1 (length vs))
       (error 'run "multiple results ~s" vs))
     (car vs)]
    [else #f]))

;; opens a visualization of the derivation
(define (show p)
  (-> e? void?)
  (show-derivations
   (build-derivations
    (⇓ · ,p Δ v))))

;; strictly speaking, this treats all variables as if they were bound
(define-metafunction L
  =α : any any ((variable variable) ...) -> (any ((variable variable) ...))
  [(=α () () any) (#t any)]
  [(=α (any_l any_l-rest ...) (any_r any_r-rest ...) any_env) ;; check one, then check the rest
   ,(redex-let* L ([(any_first-res any_new-env) 
                    (term (=α any_l any_r any_env))]
                   [(any_rest-res any_done-env)
                    (term (=α (any_l-rest ...) (any_r-rest ...) any_new-env))])
      (term (,(and (term any_first-res) (term any_rest-res)) any_done-env)))]
  [(=α variable_l variable_r (name env (any_before ... (variable_l variable_r) any_after ...)))
   (#t env)] ;; in environment already
  [(=α (name variable_left variable_!_l) (name variable_right variable_!_r) 
       (name env ((variable_!_l variable_!_r) ...)))
   (#t ,(cons (term (variable_left variable_right)) ;; add to environment
              (term env)))]
  [(=α any any any_env)
   (#t any_env)]
  [(=α any any_different any_env)
   (#f any_env)])


(define-syntax-rule (test-α-equal lhs rhs)
  (if (car (term (=α ,lhs ,rhs ())))
      (test-equal lhs lhs)   ;; hack: run a fake test
      (test-equal lhs rhs))) ;; this will fail
  


(module+ test

  ;; replace-free and rename-bound tests omitted, since those metafunctions are gone

  (test-α-equal (term (subst (λ (x) ((λ (y) x) y)) y z))
                (term (λ (x) ((λ (y) x) z))))
  (test-α-equal (term (subst (λ (x) ((λ (y) y) y)) y z))
                (term (λ (x) ((λ (y) y) z))))
  (test-α-equal (term (subst (λ (x) ((λ (q) y) y)) y z))
                (term (λ (x) ((λ (q) z) z))))
  (test-α-equal (term (subst (λ (y) x) x y))
                (term (λ (y1) y)))
  (test-α-equal (term (subst (let ([x 1]) (+ x z)) z q))
                (term (let ([x 1]) (+ x q))))
  (test-α-equal (term (subst (let ([x 1][y 2][z 3]) (+ x y)) x q))
                (term (let ([x 1][y 2][z 3]) (+ x y))))
  
  (test-α-equal (term (separate · x)) (term ⊥))
  (test-α-equal (term (separate (· x ↦ 1) x)) (term (· x ↦ 1)))
  (test-α-equal (term (separate ((· x ↦ 1) y ↦ 2) x)) 
                (term ((· y ↦ 2) x ↦ 1)))
  (test-α-equal (term (separate (· x ↦ 1) y)) (term ⊥))

  ;; ^ tests omitted, since that metafunction is gone

  (test-α-equal (judgment-holds (⇓ (· y ↦ 1) ((λ (x) x) y) Δ v) v)
                (list (term 1)))
  
  (test-α-equal (run (term 1)) 1)
  (test-α-equal (run (term (let ([y 1]) 
                             (let ([z ((λ (x) x) y)])
                               2))))
                2)
  (test-α-equal (run (term (let ([y 1]) y))) 1)
  (test-α-equal (run (term (let ([y (λ (x) x)]) y))) (term (λ (x1) x1)))
  (test-α-equal (run (term (let ([y 1]) ((λ (x) x) y)))) 1)
  (test-α-equal (run (term
                      (let ([app (λ (f) (λ (x) (f x)))]
                            [f (λ (x) (λ (y) x))]
                            [o 1])
                        (((app f) o) f))))
                1)
  (test-α-equal (run (term (if0 0 1 2))) 1)
  (test-α-equal (run (term (if0 1 2 3))) 3)
  
  ;; free variable errors return no derivation
  (test-α-equal (run (term (let ([x y]) x))) #f)
  
  ;; as do runtime errors
  (test-α-equal (run (term (let ([two 2]) (1 two)))) #f)
  
  (test-α-equal (run
                 (term
                  (let ([o 1]
                        [t 2]
                        [r 3]
                        [f 4])
                    (((((λ (x)
                           (λ (y)
                              (λ (z)
                                 (λ (w)
                                    (+ (+ x y)
                                       (+ w z))))))
                        o)
                       t)
                      r)
                     f))))
                10)
  
  (test-α-equal (run (term
                      (let ([me (λ (x) x)])
                        (let ([tri
                               (λ (x)
                                  (let ([x1 (+ x -1)])
                                    (+ (me x1) x)))]
                              [five 5])
                          (tri five)))))
                9)
  
  (test-α-equal (run (term (let ([tri
                                  (λ (x)
                                     (let ([x1 (+ x -1)])
                                       x))]
                                 [five 5])
                             (tri five))))
                5)
  
  (test-α-equal (run (term
                      (let ([Y (λ (f) 
                                  (let ([g (λ (x) 
                                              (let ([xx (x x)])
                                                (f xx)))])
                                    (g g)))]
                            [tri
                             (λ (me)
                                (λ (x)
                                   (if0 x
                                        0
                                        (let ([x1 (+ x -1)])
                                          (+ (me x1) x)))))]
                            [five 5])
                        ((Y tri) five))))
                (+ 5 4 3 2 1 0))


  (test-α-equal (run (term (let ([one 1] [two 2])
                             (((λ (x) (λ (x) (+ x one))) one) two))))
                3)
  
  (test-results))
