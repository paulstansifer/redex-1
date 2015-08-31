#lang racket

(module+ test         
  (require rackunit)
  (require redex/reduction-semantics)

  (define (all-distinct? . lst)
    (equal? lst (remove-duplicates lst)))

  (define-language lc
    (x variable-not-otherwise-mentioned)
    (expr x
          (expr expr)
          (lambda (x) expr))
    #:binding-forms
    (lambda (x) expr #:refers-to x))
  
  (check-match
   (redex-let* lc
               ([(lambda (x) expr) (term (lambda (x) (y (lambda (y) (y (y x))))))])
               (term (lambda (x) expr)))
   `(lambda (,x) (y (lambda (y) (y (y ,x)))))
   (all-distinct? x 'x 'y))
  
  ;; naively-written substitution
  ;;(should be capture-avoiding, thanks to #:binding-forms)
  
  (define-metafunction lc
    subst : any x any -> any
    [(subst x x any_new) any_new]
    [(subst x x_old any_new) x]
    [(subst (any ...) x_old any_new)
     ((subst any x_old any_new) ...)]
    [(subst any x_old any_new) any]) 

  
  (check-match
   (term (subst (lambda (x) (y (lambda (y) (y y)))) y (lambda (z) (z x))))
   `(lambda (,x) ((lambda (z) (z x)) (lambda (,y) (,y ,y))))
   (all-distinct? x y `x `y))


  ;; == more complex stuff ==

  (define-language big-language
   (expr (expr expr)
         (lambda (x) expr)
         (va-lambda (x ...) expr)
         (va-vb-lambda (x ...) expr ...)
         (ieie x x x expr expr)
         (let* clauses expr)
         (let3* ((x_a expr_a) (x_b expr_b) (x_c expr_c)) expr_body)
         (siamese-lambda ((x ...) expr) ...)
         (pile-o-binders x ...)
         (boring-...-bind (x x ... x))
         (natural-let* ((x expr) ...) expr)
         x
         number
         (+ expr ...))
   (clauses (cl x expr clauses)
            no-cl)
   (x variable-not-otherwise-mentioned)
   #:binding-forms
   (lambda (x) expr #:refers-to x)
   (va-lambda (x ...) expr #:refers-to (rib x ...))
   (va-vb-lambda (x ...) expr #:refers-to (rib x ...) ...)
   (ieie x_i x_e x_ie expr_1 #:refers-to (shadow x_ie x_i)
         expr_2 #:refers-to (shadow x_i x_ie)) #:exports (shadow x_e x_ie)
   (let* clauses expr #:refers-to clauses)
   (cl x expr clauses #:refers-to x) #:exports (shadow clauses x)
   (let3* ((x_a expr_a) (x_b expr_b #:refers-to x_a) 
           (x_c expr_c #:refers-to (shadow x_b x_a)))
          expr_body #:refers-to (shadow x_c x_b x_a))
   (siamese-lambda ((x ...) expr #:refers-to (rib x ...)) ...)
   (embedded-lambda (x) (((x) expr) expr) )
   (pile-o-binders x ...) #:exports (rib x ...)
   (boring-...-bind (x_1 x_2 #:...bind (whatever nothing nothing) x_3))
   (natural-let* ((x expr) #:...bind (clauses x (shadow clauses x))) expr_body #:refers-to clauses)

   ;; TODO: either fix this, or make it error reasonably
   #;
   (wacky-...-bind x_out ((x_in x_side x_exp expr  #:refers-to x_out ) 
                          #:...bind (clauses x_side (rib x_exp clauses)))
                   expr_body #:refers-to (rib x_in ...))
   )

  

  ;; a no-op, except that it triggers freshening
  (define-metafunction big-language
    freshen-all-the-way-down : any -> any
    [(freshen-all-the-way-down (any ...))
     ((freshen-all-the-way-down any) ...)]
    [(freshen-all-the-way-down any) any])

  (define-syntax-rule (destr-test orig pat (distinct-name ...))
    (check-match (term (freshen-all-the-way-down orig))
                 `pat
                 (all-distinct? distinct-name ...)))

  (define-syntax-rule (subst-test orig old-var new-val expected (distinct-name ...))
    (check-match (substitute big-language (term orig) (term old-var) (term new-val))
                 `expected
                 (all-distinct? distinct-name ...)))

  (define-syntax-rule (destr-test-lang lang orig pat (distinct-name ...))
    (begin 
      (define-metafunction lang
        fatwd : any -> any
        [(fatwd (any (... ...)))
         ((fatwd any) (... ...))]
        [(fatwd any) any])
      
      (check-match (term (fatwd orig))
                   `pat
                   (all-distinct? distinct-name ...))))

  ;; capture-avoiding substitution

  (subst-test (lambda (x) (a (b (lambda (a) (a b)))))
              a (lambda (y) (x y))
              (lambda (,xx) ((lambda (y) (x y)) (b (lambda (,aa) (,aa b)))))
              ('a 'b 'x 'y xx aa))

  (define-syntax-rule (aeq lhs rhs)
    (alpha-equivalent? big-language (term lhs) (term rhs)))

  ;; alpha-equivalence tests

  (parameterize 
   [(default-language big-language)]

   (check-equal? (aeq (lambda (x) x) (lambda (x) x)) #t)

   (check-equal? (aeq (lambda (xxxxx) xxxxx) (lambda (y) y)) #t)

   (check-equal? (aeq (lambda (x) x) (lambda (x) y)) #f)

   (check-equal? (aeq 
                      (lambda (x) (lambda (y) (x y)))
                      (lambda (y) (lambda (x) (y x)))) 
                 #t)
   
   (check-equal? (aeq 
                      (lambda (y) (lambda (x) (x y)))
                      (lambda (y) (lambda (x) (y x)))) 
                 #f)

   (check-equal? (aeq 
                      (lambda (y) (lambda (a) a))
                      (lambda (y) (lambda (b) b))) 
                 #t)
   
   (check-equal? (aeq
                      (x (lambda (x) x))
                      (y (lambda (y) y)))
                 #f)
   
   (check-equal? (aeq
                      (a (lambda (x) x))
                      (a (lambda (y) y)))
                 #t)
   
   (check-equal? (aeq
                      (va-vb-lambda (a b c) a b c d)
                      (va-vb-lambda (x y z) x y z d))
                 #t)
   
   (check-equal? (aeq
                      (va-vb-lambda (a b c) a b c d)
                      (va-vb-lambda (x y z) x y c d))
                 #f)

   (check-equal? (aeq a (a)) #f)

   (check-equal? (aeq (b) (a)) #f)

   (check-equal? (aeq (((a) a) a) (((b) a) a)) #f)
   
   (check-equal? (aeq (((a) a) a) (((a) a) a)) #t)

   (check-equal? (aeq
                      (let* (cl a x (cl b (a 5) (cl c (b (a 6)) no-cl))) (a (b c)))
                      (let* (cl aa x (cl bb (aa 5) (cl cc (bb (aa 6)) no-cl))) (aa (bb cc))))
                 #t)

   (check-equal? (aeq
                      (let* (cl a x (cl b (a 5) (cl c (b (a 6)) no-cl))) (a (b c)))
                      (let* (cl aa x (cl bb (aa 5) (cl cc (bb (a 6)) no-cl))) (aa (bb cc))))
                 #f)

   (check-equal? (aeq
                      (let* (cl a x (cl b (a 5) (cl c (b (a 6)) no-cl))) (a (b c)))
                      (let* (cl aa x (cl bb (aa 5) (cl cc (bb (aa 6)) no-cl))) (aa (bb c))))
                 #f)

   (check-equal? (aeq
                      ((lambda (x) x) 8)
                      ((lambda (y) y) 8))
                 #t)

   (check-equal? (aeq
                      ((lambda (x) (lambda (y) (x y))) 8)
                      ((lambda (y) (lambda (x) (x y))) 8))
                 #f)

   ;; tests for https://github.com/paulstansifer/redex/issues/10

   (check-equal? (aeq
                      (1 2 3 (cl f (lambda (x) x) no-cl))
                      (1 2 3 (cl f (lambda (y) y) no-cl)))
                 #t)

   (check-equal? (aeq
                      (1 2 3 (cl f (lambda (x) x) no-cl))
                      (1 2 3 (cl g (lambda (x) x) no-cl)))
                 #f)

   (check-equal? (aeq
                      (pile-o-binders a b c)
                      (pile-o-binders x y z))
                 #f)

   (check-equal? (aeq
                      ((pile-o-binders a b c))
                      ((pile-o-binders x y z)))
                 #f)

   (check-equal? (aeq
                  ((natural-let* ((a (+ a b c)) (b (+ a b c)) (c (+ a b c))) (+ a b c)))
                  ((natural-let* ((aa (+ a b c)) (bb (+ aa b c)) (cc (+ aa bb c))) (+ aa bb cc))))
                 #t)

   (check-equal? (aeq
                  ((natural-let* ((a (+ a b c)) (b (+ a b c)) (c (+ a b c))) (+ a b c)))
                  ((natural-let* ((aa (+ a b c)) (bb (+ aa b c)) (cc (+ aa bb cc))) (+ aa bb cc))))
                 #f)
   
   )
  (destr-test
   (1 2 3 (cl f (lambda (x) x) no-cl))
   (1 2 3 (cl f (lambda (,xx) ,xx) ,no-cl))
   ('f 'x xx))
  

  ;; TODO: the `no-cl` shouldn't be freshened. Doing proper pattern compilation
  ;; should get rid of that problem
  
  (destr-test
   (lambda (x) (let* (cl x 5 no-cl) x))
   (lambda (,x-outer) (let* (cl ,x-inner 5 ,no-cl) ,x-inner))
   (x-outer x-inner 'x))

  (destr-test
   (let* (cl a 4 (cl b (a 5) (cl c (b (a 6)) no-cl))) (a (b c)))
   (let* (cl ,aa 4 (cl ,bb (,aa 5) (cl ,cc (,bb (,aa 6)) ,no-cl))) (,aa (,bb ,cc)))
   ('a aa 'b bb 'c cc))

  (destr-test
   (let* (cl  a 1 (cl  a  a no-cl))  a)
   (let* (cl ,a 1 (cl ,b ,a ,no-cl)) ,b)
   (a b 'a))

  #;(term (freshen-all-the-way-down (let* (cl a a no-cl) a)))


  ;; TODO: what should we do about metafunction caching?
  
  (destr-test
   (let* (cl a ((lambda (a) a) a) 
             (cl x ((lambda (a) a) a) no-cl)) a)
   (let* (cl ,a1 ((lambda (,a2) ,a2) a) 
             (cl ,x ((lambda (,a3) ,a3) ,a1) ,no-cl)) ,a1)
   (a1 a2 'a))  ;; (once metafunction caching is fixed, add a3 to this list)

  (destr-test
   (va-lambda (a b c) (+ c b a))
   (va-lambda (,a1 ,b1 ,c1) (+ ,c1 ,b1 ,a1))
   (a1 b1 c1 'a 'b 'c))

  (destr-test
   (va-lambda (a b c) (va-lambda (a b c) (+ a b c)))
   (va-lambda (,a2 ,b2 ,c2) (va-lambda (,a1 ,b1 ,c1) (+ ,a1 ,b1 ,c1)))
   (a1 b1 c1 a2 b2 c2 'a 'b 'c))

  (destr-test
   (va-vb-lambda (a b c) (+ c b a) a b c)
   (va-vb-lambda (,a1 ,b1 ,c1) (+ ,c1 ,b1 ,a1) ,a1 ,b1 ,c1)
   (a1 b1 c1 'a 'b 'c))
  
  ;; #:...bind tests

  (destr-test
   (boring-...-bind (a b c d e f))
   (boring-...-bind (a b c d e f))
   ())

  (destr-test
   (natural-let* ((a (+ a b c d))
                  (b (+ a b c d))
                  (c (+ a b c d))
                  (d (+ a b c d)))
      (+ a b c d))
   (natural-let* ((,a (+ a b c d))
                  (,b (+ ,a b c d))
                  (,c (+ ,a ,b c d))
                  (,d (+ ,a ,b ,c d)))
      (+ ,a ,b ,c ,d))
   (a b c d 'a 'b 'c 'd)
   )

  (destr-test 
   (natural-let* ((a 
                   (natural-let* ((a (+ a b c))
                                  (b (+ a b c)))
                     (+ a b)))
                  (b (+ a b c))
                  (c (+ a b c)))
     (natural-let* ((a a)
                    (b (+ a b)))
       (+ a b c)))
   (natural-let* ((,a 
                   (natural-let* ((,aa (+ a b c))
                                  (,bb (+ ,aa b c)))
                     (+ ,aa ,bb)))
                  (,b (+ ,a b c))
                  (,c (+ ,a ,b c)))
     (natural-let* ((,aaa ,a)
                    (,bbb (+ ,aaa ,b)))
       (+ ,aaa ,bbb ,c)))
   (a b c aa bb aaa bbb 'a 'b 'c))
    
)
  

;; Tests for the old version; try to reincorporate these when it becomes possible.

#|
;; == tests of the internals of binding-forms ==

 (module+ test
 (require rackunit) 
 (require redex/reduction-semantics)
 
 ;; === fine-grained tests ===

 (define-syntax (setup-binding-forms stx)
   (syntax-case stx ()
     [(setup-binding-forms lang-name (binder-info ...) body ...)
      (parameterize
       ([redex-let*-name #`redex-let*]
        [term-match/single-name #`term-match/single])

       (setup-functions
        (parse-binding-forms #`(binder-info ...) #`lang-name)
        #`lang-name
        #`(begin body ...)))]))
 
 ;; not used yet
 (define-syntax-rule (test-phase-1-fn (fn phase-0-args ...))
   (let-syntax
       ([test-phase-1-fn-helper
         (lambda (stx) (syntax-case stx ()
                         [(test-phase-1-fn) (fn phase-0-args ...)]))])
     (test-phase-1-fn-helper)))
 
 (define-language big-language
   (expr (expr expr)
         (lambda (x) expr)
         (lambda (x ...) expr)
         (ieie x x x expr expr)
         (let* clauses expr)
         (let3* ((x_a expr_a) (x_b expr_b) (x_c expr_c)) expr_body)
         (siamese-lambda ((x ...) expr) ...)
         (pile-o-binders x ...)
         x
         number)
   (clauses (cl x expr clauses)
            no-cl)
   (x variable-not-otherwise-mentioned))
 
 (setup-binding-forms big-language
   ((lambda (x) expr #:refers-to x)
    (va-lambda (x ...) expr #:refers-to (rib x ...))
    (ieie x_i x_e x_ie expr_1 #:refers-to (shadow x_ie x_i)
          expr_2 #:refers-to (shadow x_i x_ie)) #:exports (shadow x_e x_ie)
    (let* clauses expr #:refers-to clauses)
    (cl x expr clauses #:refers-to x) #:exports (shadow clauses x)
    (let3* ((x_a expr_a) (x_b expr_b #:refers-to x_a) 
            (x_c expr_c #:refers-to (shadow x_b x_a)))
           expr_body #:refers-to (shadow x_c x_b x_a))
    (siamese-lambda ((x ...) expr #:refers-to (rib x ...)) ...)
    (embedded-lambda (x) (((x) expr) expr) )
    (pile-o-binders x ...) #:exports (rib x ...))

   ;; ==== reference-rename ====
   (check-equal?
    (rename-references `((a aa)) `(a (lambda (a) (a b))))
    `(aa (lambda (a) (a b))))
   
   (check-equal?
    (rename-references `((a aa) (b bb) (c cc) (d dd) (e ee) (f ff))
                       `(ieie a b c
                              (a (b (c (d (e (f g))))))
                              (a (b (c (d (e (f g))))))))
    `(ieie a b c
           (a (bb (c (dd (ee (ff g))))))
           (a (bb (c (dd (ee (ff g))))))))

   (check-equal?
    (rename-references `((a aa))
                       `(cl a a no-cl))
    `(cl a aa no-cl))

   (check-equal?
    (rename-references `((a aa))
                       `((((cl a a no-cl)))))
    `((((cl a aa no-cl)))))

   (check-equal?
    (rename-references `((a aa))
                    `(cl a (a (lambda (a) a)) no-cl))
    `(cl a (aa (lambda (a) a)) no-cl))

   ;; ==== noop-binder-substitution ====

   (check-match
    (noop-binder-substitution `(cl a b no-cl))
    `((no-cl no-cl) (a a)))

   ;; ==== freshen/rec ====

   (check-match
    (freshen/rec
     `(ieie a b c (a (b (c d))) (a (b (c d)))))
    `((ieie a ,bb ,cc (a (b (,cc d))) (a (b (,cc d)))) ((b ,bb) (c ,cc)))
    (and (not (eq? bb `b)) (not (eq? cc `c))))
   

   ) ;; end setup-binding-forms

 
 ;; === coarse-grained tests ===


 (define-syntax (define-freshener stx)
   (syntax-case stx ()
     [(define-freshener freshener-name lang-name binder-info ...)
      #`(define freshener-name
          #,(binding-info->freshener #`(binder-info ...) #`lang-name
                                     #`redex-let* #`term-match/single))]))

 (define-freshener big-freshener
   big-language
   (lambda (x) expr #:refers-to x)
    (va-lambda (x ...) expr #:refers-to (rib x ...))
    (ieie x_i x_e x_ie expr_1 #:refers-to (shadow x_ie x_i)
          expr_2 #:refers-to (shadow x_i x_ie)) #:exports (shadow x_e x_ie)
    (let* clauses expr #:refers-to clauses)
    (cl x expr clauses #:refers-to x) #:exports (shadow clauses x)
    (let3* ((x_a expr_a) (x_b expr_b #:refers-to x_a) 
            (x_c expr_c #:refers-to (shadow x_b x_a)))
           expr_body #:refers-to (shadow x_c x_b x_a))
    (siamese-lambda ((x ...) expr #:refers-to (rib x ...)) ...)
    ;; PS: should the user be able to leave the different `expr`s unsubscribed?
    ;; The result might be unexpected if we interpret that literally
    (embedded-lambda (x_0) (((any_1) expr_1 #:refers-to any_1) expr_0) #:refers-to x_0)
    (pile-o-binders x ...) #:exports (rib x ...))


 (check-match (big-freshener `(lambda (x) x))
              `(lambda (,x) ,x) ;; structure was preserved
              (not (eq? x `x))) ;; we actually freshened the name
 
 (check-equal? (big-freshener 1) 1)


 (define (totally-destructure d v)
   (match (d v)
          [(list sub-v ...) (map (lambda (sv) (totally-destructure d sv)) sub-v)]
          [atom atom]))
 
 (define (all-distinct-vars? . lst)
   (and (equal? lst (remove-duplicates lst))
        (andmap symbol? lst)))

 (check-match
  (totally-destructure 
   big-freshener
   `(let* (cl a 4 (cl b (a 5) (cl c (b (a 6)) no-cl))) (a (b c)))ll)
  `(let* (cl ,aa 4 (cl ,bb (,aa 5) (cl ,cc (,bb (,aa 6)) no-cl))) (,aa (,bb ,cc)))
  (all-distinct-vars? 'a aa 'b bb 'c cc))

 ;; check that shadowing works properly
 (check-match
  (totally-destructure 
   big-freshener
   `(let* (cl  a 1 (cl  a  a no-cl))  a))
  ` (let* (cl ,a 1 (cl ,b ,a no-cl)) ,b)
  (not (equal? a b)))

 ;; test that renamings pay attention to the structure of what they traverse
 (check-match
  (totally-destructure
   big-freshener
   `(let* (cl a ((lambda (a) a) a) 
              (cl x ((lambda (a) a) a) no-cl)) a))
  ` (let* (cl ,a1 ((lambda (,a2) ,a2) a) 
              (cl ,x ((lambda (,a3) ,a3) ,a1) no-cl)) ,a1)
  (all-distinct-vars? a1 a2 a3 'a))
 
 ;; test that nested structure doesn't get lost

 (check-match
  (totally-destructure
   big-freshener
   `(embedded-lambda (a) (((b) (a b)) (a b))))
  ` (embedded-lambda (,aa) (((,bb) (,aa ,bb)) (,aa b)))
  (all-distinct-vars? aa bb 'a 'b))

 (check-match
  (totally-destructure
   big-freshener
   `(embedded-lambda (a) (((a) a) a)))
  ` (embedded-lambda (,aa) (((,bb) ,bb) ,aa))
  (all-distinct-vars? aa bb 'a))

 (check-match
  (totally-destructure
   big-freshener
   `(embedded-lambda (a) ((((cl a x no-cl)) a) a)))
  ` (embedded-lambda (,aa) ((((cl ,bb x no-cl)) ,bb) ,aa))
  (all-distinct-vars? aa bb 'a))

 (check-match
  (totally-destructure
   big-freshener
   `(let3* ((a 1) (b a) (c (a b)))
           (a (b c))))
  `(let3* ((,aa 1) (,bb ,aa) (,cc (,aa ,bb)))
          (,aa (,bb ,cc)))
  (and (not (equal? 'a aa)) (not (equal? 'b bb)) (not (equal? 'c cc))))


 (check-match  (totally-destructure big-freshener `(va-lambda (a b c) (a (b (c d)))))
  `(va-lambda (,a ,b ,c) (,a (,b (,c d))))
  (and (not (eq? a b))
       (not (eq? b c))
       (not (eq? c a))))

 (check-match
  (totally-destructure 
   big-freshener
   `(siamese-lambda ((a b c) (a (b (c d)))) ((a b) (b a))))
  `(siamese-lambda ((,a ,b ,c) (,a (,b (,c d)))) 
                   ((,a2 ,b2) (,b2 ,a2)))
  (and (not (eq? a a2)) (not (eq? b b2))))
 
 )

;; == tests of binding forms inside actual Redex ==

 (module+ test
  (require redex/reduction-semantics)
  
  (define-language lc
    (e (e ...)
       x
       (lambda (x) e))
    (x variable-not-otherwise-mentioned)
    #:binding-forms
    (lambda (x) e #:refers-to x))
  
  (check-match
   (redex-let* lc
               ([(lambda (x) e) (term (lambda (x) (y (lambda (y) (y (y x))))))])
               (term (lambda (x) e)))
   `(lambda (,x) (y (lambda (y) (y (y ,x)))))
   (not (eq? x `x)))

  (define-syntax-rule (define-subst subst-name lang)
    (define-metafunction lang
      subst-name : any x e -> any
      [(subst-name x x e_new) e_new]
      [(subst-name x x_old e_new) x]
      [(subst-name (any (... ...)) x_old e_new)
       ((subst-name any x_old e_new) (... ...))]
      [(subst-name any x_old e_new) any]))
  
  (define-subst subst-lc lc)
  
  
  (check-match
   (term (subst-lc (lambda (x) (y (lambda (y) (y y)))) y (lambda (z) (z x))))
   `(lambda (,x) ((lambda (z) (z x)) (lambda (,y) (,y ,y))))
   (all-distinct-vars? x y `x `y))

  )
|#

;; == interactions with `extend-language` and `union-language` ==

(module+ test
  (define-language va-lc
    (x variable-not-otherwise-mentioned)
    (expr x
          (expr ...)
          (lambda (x ...) expr))
    #:binding-forms
    (lambda (x ...) expr #:refers-to (rib x ...)))

  (define-extended-language lc-with-extra-lambda va-lc
    (expr ....
          (extra-lambda (x) expr))
    #:binding-forms
    (extra-lambda (x) expr #:refers-to x))


  ;; TODO: test a language extension consisting only of #:binding-forms

  (define (all-distinct-vars? . lst)
    (and (equal? lst (remove-duplicates lst))
         (andmap symbol? lst)))

  (define-syntax-rule (define-subst subst-name lang)
    (define-metafunction lang
      subst-name : any x any -> any
      [(subst-name x x any_new) any_new]
      [(subst-name x x_old any_new) x]
      [(subst-name (any (... ...)) x_old any_new)
       ((subst-name any x_old any_new) (... ...))]
      [(subst-name any x_old any_new) any]))

  (define-subst subst-lwel lc-with-extra-lambda)

  (check-match
   (term (subst-lwel (lambda (x) (extra-lambda (y) (x y z
                                                      (lambda (z) z)
                                                      (extra-lambda (z) z))))
                     z (w x y z)))
   `(lambda (,x) (extra-lambda (,y) (,x ,y (w x y z)
                                        (lambda (,z0) ,z0)
                                        (extra-lambda (,z1) ,z1))))
   (all-distinct-vars? x y z0 z1 `w `x `y `z))

  (define-language definition-lang
    (x variable-not-otherwise-mentioned)
    (block (blk stmt block)
           ())
    (stmt expr
          (def x expr))
    (expr (+ expr expr)
          number
          (x)) ;; this is to define plain variable references from being interpreted as binders
    #:binding-forms
    (def x expr) #:exports x
    (blk stmt block #:refers-to stmt))

  (destr-test-lang 
   definition-lang
   (blk (def a 1) (blk (+ (a) (a)) ()))
   (blk (def ,aa 1) (blk (+ (,aa) (,aa)) ()))
   (aa 'a))


  (define-union-language union-def-lc definition-lang lc)

  (destr-test-lang 
   union-def-lc
   (blk (def a 1) (blk (+ (a) (a)) ()))
   (blk (def ,aa 1) (blk (+ (,aa) (,aa)) ()))
   (aa 'a))

  (define-subst subst-udl union-def-lc)

  (check-match
   (term (subst-udl
          (blk (x) 
               (blk (z) 
                    (blk (def x (+ (lambda (z) z) (lambda (x) z)))
                         (blk (def z x)
                              (blk (z) ())))))
          z (w x y)))
   `(blk (x)
         (blk ((w x y)) 
              (blk (def ,x0 (+ (lambda (,z0) ,z0) (lambda (,x1) (w x y))))
                   (blk (def ,z1 ,x)
                        (blk (,z1) ())))))
   (all-distinct-vars? `w `x `y `z x0 x1 z0 z1))

  (define-union-language four-lcs (a. lc) (b. lc) lc (c. lc))

  (destr-test-lang 
   four-lcs
   (lambda (a) a)
   (lambda (,aa) ,aa)
   (aa 'a))

  (define-union-language pfx-def-and-lc (def. definition-lang) (lc. lc))

  (destr-test-lang 
   pfx-def-and-lc
   (lambda (a) a)
   (lambda (,aa) ,aa)
   (aa 'a))

  (destr-test-lang 
   pfx-def-and-lc
   (blk (def a 1) (blk (+ (a) (a)) ()))
   (blk (def ,aa 1) (blk (+ (,aa) (,aa)) ()))
   (aa 'a))

  
 )
