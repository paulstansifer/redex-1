#lang racket


;; == tests of the internals of binding-forms ==

(module+ test
 (require rackunit) 
 (require redex/reduction-semantics)
 (require (submod redex/private/binding-forms internals-for-testing))
 
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
 
 (define (all-distinct? . lst)
    (equal? lst (remove-duplicates lst)))

 (check-match
  (totally-destructure 
   big-freshener
   `(let* (cl a 4 (cl b (a 5) (cl c (b (a 6)) no-cl))) (a (b c))))
  `(let* (cl ,aa 4 (cl ,bb (,aa 5) (cl ,cc (,bb (,aa 6)) no-cl))) (,aa (,bb ,cc)))
  (all-distinct? 'a aa 'b bb 'c cc))

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
  (all-distinct? a1 a2 a3 'a))
 
 ;; test that nested structure doesn't get lost

 (check-match
  (totally-destructure
   big-freshener
   `(embedded-lambda (a) (((b) (a b)) (a b))))
  ` (embedded-lambda (,aa) (((,bb) (,aa ,bb)) (,aa b)))
  (all-distinct? aa bb 'a 'b))

 (check-match
  (totally-destructure
   big-freshener
   `(embedded-lambda (a) (((a) a) a)))
  ` (embedded-lambda (,aa) (((,bb) ,bb) ,aa))
  (all-distinct? aa bb 'a))

 (check-match
  (totally-destructure
   big-freshener
   `(embedded-lambda (a) ((((cl a x no-cl)) a) a)))
  ` (embedded-lambda (,aa) ((((cl ,bb x no-cl)) ,bb) ,aa))
  (all-distinct? aa bb 'a))

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
  (require rackunit)
  
  (define-language lc
    (e (e e)
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
  
  (define-metafunction lc
    subst : any x e -> any
    [(subst x x e_new) e_new]
    [(subst x x_old e_new) x]
    [(subst (any ...) x_old e_new)
     ((subst any x_old e_new) ...)]
    [(subst any x_old e_new) any])
  
  
  (check-match
   (term (subst (lambda (x) (y (lambda (y) (y y)))) y (lambda (z) (z x))))
   `(lambda (,x) ((lambda (z) (z x)) (lambda (,y) (,y ,y))))
   (all-distinct? x y `x `y)))
