#lang racket


;; These are to put markers inside Redex values
(define shadow-sym (gensym 'shadow))
(define rib-sym (gensym 'rib))

(begin-for-syntax ;; this covers most of the file; let's not indent
(require racket)
(require (for-template "binding-objects.rkt"))
(require (for-template "reduction-semantics.rkt"))
(require (for-template (only-in "term.rkt" term)))
(require (for-template (only-in "matcher.rkt" caching-enabled?)))
(require (for-template "error.rkt"))
(require "error.rkt")
(require (only-in racket/syntax generate-temporary))

(provide parse-binding-forms
         freshener
         reference-renamer
         binder-renamer
         setup-binding-forms
         binding-object-generator)


;; A binding-form is a feature of the language (e.g. `let`)
;; The only thing we need to know is how to construct one, so it's just a constructor
;; It takes a list of Redex terms and returns a binding-object

;; A binding-object is an opaque piece of syntax with binding information.
;; (see binding-objects.rkt)

(define-syntax (shadow stx) (raise-syntax-error 'shadow "used outside of binding specification"))
(define-syntax (rib stx) (raise-syntax-error 'rib "used outside of binding specification"))
(define-syntax (nothing stx) (raise-syntax-error 'nothing "used outside of binding specification"))

(struct import/internal (body beta) #:transparent)

;; === Parsing ===

;; takes the syntax that comes after a `#:binding-forms` and produces
;; an assoc of form names to an easier-to-use internal form
(define (parse-binding-forms binding-forms-stx lang-name)
  (syntax-case binding-forms-stx ()
    [((bf-name . bf-body) . rest-plus-exports)
     (begin
       ;; pull the #:exports off (it can only occur at the end of a binding form
       ;; declaration), along with all subsequent binding forms
       (define-values (rest-of-bfs exports)
         (syntax-case #'rest-plus-exports ()
           [(#:exports exports-beta . rest-of-bfs) (values #'rest-of-bfs #'exports-beta)]
           [(#:exports) (raise-syntax-error 'define-language
                                            "#:exports requires an argument"
                                            #'rest-plus-exports)]
           [(rest-of-bfs ...)
            (values #'(rest-of-bfs ...) #'nothing)]
           [_ (raise-syntax-error 'parse-binding-forms "internal error")]))

       (define str-name (symbol->string (syntax->datum #'bf-name)))

       (cons (list #'bf-name
                   (bspec/names
                    (surface-bspec->bspec #`(bf-body #:exports #,exports))
                    lang-name
                    (generate-temporary (string-append str-name "-freshen"))
                    (generate-temporary (string-append str-name "-noop-bnd-subst"))
                    (generate-temporary (string-append str-name "-ref-ren"))
                    (generate-temporary (string-append str-name "-bnd-ren"))
                    (generate-temporary (string-append str-name "-pattern-checker"))))
             (parse-binding-forms rest-of-bfs lang-name)))]
    [() '()]
    [_ (raise-syntax-error 'define-language "expected a parenthesized binding form." #`anything)]))

(struct bspec
        (body redex-pattern export-beta imported-nts exported-nts all-mentioned-nts)
        #:transparent)

;; this has the names of the redex metafunctions we generate, and the language, too
(struct bspec/names (bs lang-name freshener-name noop-binder-subst-name
                        r-renamer-name b-renamer-name
                        pattern-checker-name)
        #:transparent)

(define (surface-bspec->bspec surface-bspec)
  (define-values (sbody export-beta)
    (syntax-case surface-bspec ()
      [(b #:exports e) (values #'b #'e)]
      [_ (raise-syntax-error 'surface-bspec->bspec "expected `(body #:exports beta)`"
                             surface-bspec)]))

  ;; replaces `#:refers-to` with an easier-to-maniuplate syntax
  (define body
    (let loop [(surface-bspec sbody)
               ;; accumulate nicer syntax
               (bspec '())]
      (syntax-case surface-bspec ()
        [() bspec]
        [(#:refers-to . rest-of-body)
         (raise-syntax-error 'define-language
                             "#:refers-to requires an expression to its left"
                             #f surface-bspec)]
        [(bspec-sub #:refers-to)
         (raise-syntax-error 'define-language
                             "#:refers-to requires an argument"
                             #f surface-bspec)]
        [(sbspec-sub #:refers-to imports-beta . rest-of-body)
         (loop #'rest-of-body
               (append bspec (list (import/internal (loop #'sbspec-sub '())
                                                    #'imports-beta))))]
        
        [(sbspec-sub . rest-of-body)
         (loop #'rest-of-body
               (append bspec (list (loop #'sbspec-sub '()))))]
        [atomic-pattern #'atomic-pattern])))

  ;; strip the extra import stuff; generate a plain redex pattern 
  (define redex-pattern
    (let loop [(bpat body)]
      (match bpat
             [(import/internal bsub beta) (loop bsub)]
             [(list bsub ...) (map loop bsub)]
             [atom atom])))
  
  (define import-names (names-mentioned-in-bspec sbody))
  (define export-names (names-mentioned-in-beta export-beta 0))

  (bspec body redex-pattern export-beta import-names export-names
         (dedupe-names (append import-names export-names))))

(module+ test
 (require rackunit)

 (define (ds s)
   (match s
          [`(,a . ,b) `(,(ds a) . ,(ds b))]
          [(import/internal p beta)
           (import/internal (ds p) (ds beta))]
          [atomic (if (syntax? atomic)
                      (ds (syntax->datum atomic))
                      atomic)]))
 
 (define (desyntax-bspec b)
   (match b
          [(bspec body pattern export i-names e-names all-names)
           (bspec (ds body) (ds pattern) (ds export) (ds i-names)
                  (ds e-names) (ds all-names))]))


 (define lambda-bspec (surface-bspec->bspec #'(((x) expr #:refers-to x)
                                               #:exports nothing)))

 (define lambda-bspec/names (bspec/names lambda-bspec
                                         #'lambda-calculus
                                         #'l-f #'l-fb #'l-rr #'l-br #'l-ck))
 
 (check-equal?
  (desyntax-bspec lambda-bspec)
  (bspec `((x) ,(import/internal 'expr 'x))
         `((x) expr) 'nothing '((x 0)) '() '((x 0))))
 
 (check-equal?
  (desyntax-bspec (surface-bspec->bspec
                   #'((a b (c d #:refers-to h e) #:refers-to (shadow e b (rib nothing))
                         f g h)
                      #:exports (rib e f))))
  (bspec `(a b ,(import/internal `(c ,(import/internal `d `h) e)
                                 `(shadow e b (rib nothing))) f g h)
         `(a b (c d e) f g h)
         `(rib e f) `((h 0) (e 0) (b 0)) `((e 0) (f 0)) `((h 0) (e 0) (b 0) (f 0))))



 ;; imported, exported, imported and exported
 (define ieie-bspec
   (surface-bspec->bspec
    #'((i e ie expr_1 #:refers-to (shadow ie i) expr_2 #:refers-to (shadow i ie))
       #:exports (shadow e ie))))

 (define ieie-bspec/names
   (bspec/names ieie-bspec #f #f #f #f #f #f))
 
 )

(define (name-assoc n lst)
  (assf (lambda (x) (bound-identifier=? x n)) lst))

(define (boolify v)
  (if v #t #f))



;; When these functions talk about names, they mean assocs from names to numbers
;; (the number being how many `...`s the name is underneath)

(define (dedupe-names lst)
  (remove-duplicates
   lst
   (match-lambda*
    [`((,id-a ,depth-a) (,id-b ,depth-b))
     (if (bound-identifier=? id-a id-b)
         (if (= depth-a depth-b)
             #t
             (redex-error #f "Same name used at two different ... depths: ~s (depth ~s) vs. ~s (depth ~s)"
                          id-a depth-a id-b depth-b))
         #f)])))


(define (has-name? lst n) ;; second is the depth
  (memf (lambda (x) (bound-identifier=? (first x) n)) lst))

;; TODO: this is handling syntax; maybe it should be vanilla data?
(define (names-mentioned-in-beta beta depth)
  (dedupe-names (names-mentioned-in-beta/rec beta depth)))

(define (names-mentioned-in-beta/rec beta depth)
  (syntax-case beta (nothing ...)
    [nothing '()]
    [(op beta (... ...) . betas)
     (append (names-mentioned-in-beta/rec #'beta (+ depth 1))
             (names-mentioned-in-beta/rec #'(op . betas) depth))]
    [(op beta . betas)
     (append (names-mentioned-in-beta/rec #'beta depth)
             (names-mentioned-in-beta/rec #'(op . betas) depth))]
    [(op) '()]
    [name `((,#'name ,depth))]))

;; TODO: this is handling surface bspecs; it should get normal bspecs
(define (names-mentioned-in-bspec/rec bspec depth)
  (syntax-case bspec (...)
    [() '()]
    [(bspec-sub (... ...) . rest)
     (append (names-mentioned-in-bspec/rec #'bspec-sub (+ depth 1))
             (names-mentioned-in-bspec/rec #'rest depth))]
    [(bspec-sub #:refers-to beta (... ...) . rest)
     (append (names-mentioned-in-bspec/rec #'bspec-sub (+ depth 1))
             (names-mentioned-in-beta #'beta (+ depth 1))
             (names-mentioned-in-bspec/rec #'rest depth))]
    [(bspec-sub #:refers-to beta . rest)
     (append (names-mentioned-in-bspec/rec #'bspec-sub depth)
             (names-mentioned-in-beta #'beta depth)
             (names-mentioned-in-bspec/rec #'rest depth))]
    [(bspec-sub . rest)
     (append (names-mentioned-in-bspec/rec #'bspec-sub depth)
             (names-mentioned-in-bspec/rec #'rest depth))]
    [plain '()]))

(define (names-mentioned-in-bspec bspec)
  (dedupe-names (names-mentioned-in-bspec/rec bspec 0)))

(module+
 test

 (define (ds-lst lst) (map (match-lambda [`(,x ,depth)
                                          `(,(syntax->datum x) ,depth)]) lst))
 
 (check-equal? (ds-lst (names-mentioned-in-beta #`a 0)) `((a 0)))
 (check-equal? (ds-lst (names-mentioned-in-beta #`(shadow (rib a b c) (shadow b c d e)
                                                          (rib f nothing g h a a a) b
                                                          nothing nothing) 0))
               (map (lambda (x) `(,x 0)) `(a b c d e f g h)))

 (check-equal? (ds-lst (names-mentioned-in-bspec #`((x) e #:refers-to x))) `((x 0)))
 (check-equal? (ds-lst (names-mentioned-in-bspec #`((x) e))) `())
 (check-equal? (ds-lst (names-mentioned-in-bspec #`(x_11
                                                    e_1 #:refers-to (shadow x_2 x_444)
                                                    (x_22 x_33 #:refers-to (rib x_1 x_2)
                                                          (e_2 e_3 #:refers-to (rib x_9))
                                                          #:refers-to x_3))))
               (map (lambda (x) `(,x 0)) `(x_2 x_444 x_1 x_9 x_3)))
 )


(define (reference-renamer-transcriber σ bs)
  (let loop [(body (bspec-body bs))]
    (match body
           [(import/internal sub-body beta) (loop sub-body)]
           [(list sub-body ...) (datum->syntax #f (map loop sub-body))]
           [atom
            (if (has-name? (bspec-all-mentioned-nts bs) atom)
                #`,(if (symbol? (term #,atom))
                        (term #,atom)
                        (rename-references (term #,σ) (term #,atom)))
                #`,(rename-references (term #,σ) (term #,atom)))])))

(define (reference-renamer bs/n)
  (define bs (bspec/names-bs bs/n))
  ;; We want a Redex `...`, not a #` one
  (define σ #`((variable_from variable_to) (... ...)))
  
  #`(define-metafunction #,(bspec/names-lang-name bs/n)
      [(#,(bspec/names-r-renamer-name bs/n)  #,σ
        (variable_binding-form-name . #,(bspec-redex-pattern bs)))
       (variable_binding-form-name . #,(reference-renamer-transcriber σ bs))]))


(define (binder-renamer-transcriber σ bs)
  (let loop [(body (bspec-body bs))]
    (match body
           [(import/internal sub-body beta) (loop sub-body)]
           [(list sub-body ...) (datum->syntax #f (map loop sub-body))]
           [atom
            (if (has-name? (bspec-all-mentioned-nts bs) atom)
                #`,(if (symbol? (term #,atom))
                       (rename-binders (term #,σ) (term #,atom))
                       (term #,atom))
                atom)])))

(define (binder-renamer bs/n)
  (define bs (bspec/names-bs bs/n))
  ;; We want a Redex `...`, not a #` one
  (define σ-redex-repr #`((variable_from variable_to) (... ...)))

  #`(lambda (σ v)
      (redex-let #,(bspec/names-lang-name bs/n)
        ([#,σ-redex-repr σ]
         [(variable_binding-form-name . #,(bspec-redex-pattern bs)) v])
        (term (variable_binding-form-name
               . #,(binder-renamer-transcriber σ-redex-repr bs))))))



(module+ test
 (check-equal?
  (syntax->datum (reference-renamer-transcriber #'σ lambda-bspec))
  '((,(if (symbol? (term x)) (term x) (rename-references (term σ) (term x))))
     ,(rename-references (term σ) (term expr))))

 (check-match
  (syntax->datum (reference-renamer lambda-bspec/names))
  `(define-metafunction ,_
     [(,_ ((,v-f ,v-t) ,_) (,bf-name (x) expr))
      (,bf-name . ,_)])))

;; TODO: this also seems to fire if the binding form doesn't match
;; the corresponding pattern in the language. A great thing to test...
;; but I don't know how it's being tested
(define (pattern-checker bs/n)
  (define bs (bspec/names-bs bs/n))
  #`(define-metafunction #,(bspec/names-lang-name bs/n)
      [(#,(bspec/names-pattern-checker-name bs/n)
        ;; doesn't check the head symbol, but since that's used to *find* the
        ;; binding form, I can't imagine that being a problem
        (variable_binding-form-name . #,(bspec-redex-pattern bs)))
       #t]
      [(#,(bspec/names-pattern-checker-name bs/n) any)
       ,(redex-error #f
         "cannot construct ~a; it does not match the pattern ~a from its binding spec"
         (term any) '(_ . #,(bspec-redex-pattern bs)))]))


;; === Beta handling ===

;; Given a beta...
;; ...produces a metafunction body that merges substitutions in a way that
;; respects the beta's shadowing.
;; `renaming-info` indicates what to substitute the nonterminal references with.
;; Only the substitution is used; the name of the bfreshened value is ignored
;; (along with `interp-beta`, this corresponds to 〚β〛(σ…) in the paper)
(define (beta->subst-merger beta renaming-info)
  (define body
    (let loop ([beta beta])
      (syntax-case beta (shadow rib nothing ...)
        [nothing #`()] ;; empty literal substitution
        [(rib . sub-betas) #`(,rib-sym #,@(map loop (syntax->list #`sub-betas)))]
        [(shadow . sub-betas) #`(,shadow-sym #,@(map loop (syntax->list #`sub-betas)))]
        [(... ...) #`(... ...)]
        [nt-ref (caddr (name-assoc #`nt-ref renaming-info))])))
  #`(interp-beta (term #,body)))

(module+ test
  (check-equal?
   (syntax->datum (beta->subst-merger #'nothing '()))
   `(interp-beta (term ())))

  (check-match
   (syntax->datum (beta->subst-merger #'(rib a (shadow a a)) `((,#'a - ,#'((x xx))))))
   `(interp-beta (term (,r ((x xx)) (,s ((x xx)) ((x xx))))))
   (and (equal? r '(unquote rib-sym)) (equal? s '(unquote shadow-sym))))

  (check-match
   (syntax->datum
    (beta->subst-merger
     #'(rib (shadow (rib a b (... ...) (rib) (shadow)) (rib c d) nothing (shadow e f))
            g h)
     `((,#'a - A) (,#'b - B) (,#'c - C) (,#'d - D)
       (,#'e - E) (,#'f - F) (,#'g - G) (,#'h - H))))
   `(interp-beta (term (,r (,s (,r A B ,ddd (,r) (,s)) (,r C D) () (,s E F)) G H)))
   (eq? ddd '...)))

 




;; === Freshening ===
;; Motto: Freshen a binder iff it is exported to the top level, but no further.
;; Every import needs to be renamed according to the sets of binders it imports


;; wrap a piece of syntax in the appropriate number of `...`s 
(define (wrap... stx depth)
  (if (= depth 0)
      stx
      #`(#,(wrap... stx (- depth 1)) (... ...))))

;; exported-nts is a list of nonterminals
(define (bfreshener renaming-info exported-nts)
  (map
   (match-lambda
    [`(,mentioned-nt ,bfreshened ,vpat ,depth)
     #`(where #,(wrap... #`(#,bfreshened #,vpat) depth)
              ;; Is the name being exported to the top level?
              #,(wrap...
                 #`,(if (xor #,(boolify (has-name? exported-nts mentioned-nt))
                             (term any_top-level?))
                        (destructure/rec (term #,mentioned-nt))
                        ;; If not, then the names are either free (and must not be
                        ;; renamed), or they will not become free by this destructuring
                        ;; (and thus don't need to be renamed)
                        (term (#,mentioned-nt ;; the value is not affected
                               ;; to participate in shadowing correctly
                               ;; without changing anything
                               ,(noop-binder-substitution (term #,mentioned-nt)))))
                 depth))])
   renaming-info))

(module+ test
         (check-equal?
          (map syntax->datum (bfreshener
                              `((,#'b1 b1_ren σ_b1 0)
                                (,#'b2 b2_ren σ_b2 0))
                              `((,#'b1 0))))
          '((where (b1_ren σ_b1)
                   ,(if (xor #t (term any_top-level?))
                        (destructure/rec (term b1))
                        (term (b1 ,(noop-binder-substitution (term b1))))))
            (where (b2_ren σ_b2)
                   ,(if (xor #f (term any_top-level?))
                        (destructure/rec (term b2))
                        (term (b2 ,(noop-binder-substitution (term b2))))))))

         (check-equal?
          (map syntax->datum (bfreshener
                              `((,#'b0 b0_ren σ_b0 0)
                                (,#'b1 b1_ren σ_b1 1)
                                (,#'b2 b2_ren σ_b2 2))
                              `()))
          '((where (b0_ren σ_b0)
                   ,(if (xor #f (term any_top-level?))
                        (destructure/rec (term b0))
                        (term (b0 ,(noop-binder-substitution (term b0))))))
            (where ((b1_ren σ_b1) ...)
                   (,(if (xor #f (term any_top-level?))
                        (destructure/rec (term b1))
                        (term (b1 ,(noop-binder-substitution (term b1))))) ...))
            (where (((b2_ren σ_b2) ...) ...)
                   ((,(if (xor #f (term any_top-level?))
                        (destructure/rec (term b2))
                        (term (b2 ,(noop-binder-substitution (term b2))))) ...) ...))))
         )

;; renaming-info is an assoc:
;; (nonterminal reference, freshened version, "name" of its renaming, depth)
;; Complicating matters, we can't name the renaming as a whole
;; (we don't know what Redex language we're in), so we need to
;; call the renaming by a pattern like `((variable_from-98 variable_to-98) ...)' 
;; (list (list identifier identifier renaming natural) ...)
(define (make-renaming-info mentioned-nts)
  (map
   (match-lambda
    [`(,mentioned-nt-stx ,depth)
     (define s (symbol->string (syntax->datum mentioned-nt-stx)))
     `(,mentioned-nt-stx
       ;; name for the result of freshening binders
       ;; (with the binders and all buried imports renamed)
       ,(generate-temporary (string-append s "_with-binders-freshened"))
       ,#`((#,(generate-temporary (string-append "variable_from" s))
            #,(generate-temporary (string-append "variable_to" s))) (... ...))
       ,depth)])
   mentioned-nts))

;; TODO: when we rename binders, we also need to rename all names bound to them 
;; in the terms that export them!

(define (freshener bs/n)
  (define bs (bspec/names-bs bs/n))

  ;; An assoc mapping nonterminal references (that have been imported)
  ;; to their freshened version and to the names of the renamings that
  ;; need to be applied.
  ;; Complicating matters, we can't name the renaming as a whole
  ;; (we don't know what Redex language we're in), so we need to
  ;; call the renaming by a pattern like `((variable_from-98 variable_to-98) ...)' 
  (define renaming-info (make-renaming-info (bspec-all-mentioned-nts bs)))
 
  (define transcriber
    (let loop [(body (bspec-body bs))]
      (match body
        [`() #`()]
        [(import/internal body-sub beta)
         #`,(rename-references #,(beta->subst-merger beta renaming-info)
                               (term #,(loop body-sub)))]
        [`(,body-sub . ,rest-of-body)
         #`(#,(loop body-sub) . #,(loop rest-of-body))]
        [nt
         (match
          (name-assoc nt renaming-info)
          [`(,_ ,bfreshened-version-of-nt ,_ ,_) bfreshened-version-of-nt]
          [#f
           #`,(if (symbol? (term #,nt)) 
                  (term #,nt) ;; atoms that aren't imported or exported are references
                  ;; TODO: this minor corner case might slow things down.
                  ;; Suggested optimization: bail out early in the very
                  ;; common case where #,nt exports nothing.
                  ;; 
                  ;; What's going on here is that, if an nt has free binders,
                  ;; but doesn't get imported or exported, they still need to
                  ;; be freshened. (effectively, they're imported into zero places)
                  ;; It's a shame, binders that don't get imported/exported
                  ;; have no use at all! But our clients might implement
                  ;; a perfectly reasonable language, which their clients
                  ;; will use in this way, so it should work right.
                  (first (destructure/rec (term #,nt))))])])))

  
  
  #`(define-metafunction #,(bspec/names-lang-name bs/n)
      [(#,(bspec/names-freshener-name bs/n) ;; name of the whole darn metafunction
        (variable_binding-form-name . #,(bspec-redex-pattern bs)) any_top-level?)
       ((variable_binding-form-name . #,transcriber) ;; new version of argument
        ;; subst that higher level forms should be consistent with:
        , #,(beta->subst-merger (bspec-export-beta bs) renaming-info))
         ;; The necessary `where` clauses to generate the renamings that we'll use
       #,@(bfreshener renaming-info (bspec-exported-nts bs))])
  )


(module+ test
         
 (define uq 'unquote) ;; oh boy
         
 (check-match
  (syntax->datum (freshener lambda-bspec/names))
  `(define-metafunction ,_
     [(,_ (,bf-name (x) expr) any_top-level?)
      ((,bf-name
        (,x-bfreshened)
        (,uq (rename-references
              (interp-beta (term ,x-σ))
              (term
               (,uq (if (symbol? (term expr))
                        (term expr)
                        (first (destructure/rec (term expr)))))))))
       (,uq (interp-beta (term ()))))
      (where (,x-bfreshened ,x-σ)
             (,uq (if (xor #f (term any_top-level?))
                      (destructure/rec (term x))
                      (term (x (,uq (noop-binder-substitution (term x))))))))]))
 
 (check-match
  (syntax->datum (freshener ieie-bspec/names))
  `(define-metafunction ,_
     [(,_ (,bf-name ,i ,e ,ie ,expr_1 ,expr_2) any_top-level?)
      ((,bf-name
        ,i-ren
        ,e-ren
        ,ie-ren
        (,uq (rename-references
              (interp-beta (term (,shad ,ie-σ ,i-σ))) ,_))
        (,uq (rename-references
              (interp-beta (term (,shad ,i-σ ,ie-σ))) ,_)))
       (,uq (interp-beta (term (,shad ,e-σ ,ie-σ)))))
      (where (,ie-ren ,ie-σ) ,_)
      (where (,i-ren ,i-σ) ,_)
      (where (,e-ren ,e-σ) ,_)]))
 )

(define (noop-substituter bs/n)
  (define bs (bspec/names-bs bs/n))

  (define renaming-info (make-renaming-info (bspec-exported-nts bs)))

  (define where-σs
    (map
     (match-lambda
      [`(,nt ,_ ,σ ,depth)
       #`(where #,(wrap... σ depth)
                #,(wrap... #` ,(noop-binder-substitution (term #,nt)) depth))])
     renaming-info))

  #`(define-metafunction #,(bspec/names-lang-name bs/n)
      [(#,(bspec/names-noop-binder-subst-name bs/n)
        (variable_binding-form-name . #,(bspec-redex-pattern bs)))
       , #,(beta->subst-merger (bspec-export-beta bs) renaming-info)
         #,@where-σs]))

(module+ test
 (check-match
  (syntax->datum (noop-substituter lambda-bspec/names))
  `(define-metafunction ,mf-name
     [(,_ ,bf) (,uq (interp-beta (term ())))])) ;; lambda doesn't export anything

 
 (check-match
  (syntax->datum (noop-substituter ieie-bspec/names))
  `(define-metafunction ,mf-name
     [(,_ (,bf-name ,i ,e ,ie ,expr_1 ,expr_2))
      (,uq (interp-beta (term (,shadow ,e-σ ,ie-σ))))
      (where ,e-σ (,uq (noop-binder-substitution (term ,e))))
      (where ,ie-σ (,uq (noop-binder-substitution (term ,ie))))])))


(module+ test
 (define let*-clause-bspec
   (surface-bspec->bspec #'((x expr_val let*-clause_next #:refers-to x)
                            #:exports (shadow x let*-clause_next)) ))
 (define let*-clause-bspec/names
   (bspec/names let*-clause-bspec #'scheme #'wh #'at #'ev #'er #'rr))

 ;; TODO: check binder-freshening behavior
 )



;; === Tying everything together ===

(define (binding-object-generator bs/n)  
  #`(letrec
        ((make-binding-object
          ;; TODO: forbid `variable-prefix`, `side-condition`, and
          ;; plain symbols in binding patterns because (a) they're unnecessary
          ;; and (b) they could make `ref-rename` and `bnd-rename` generate
          ;; binding-objects that the metafunctions would fail to match on.
          (lambda (v [check-pattern? #t])
            (cond [check-pattern?
                   ;; call the metafunction for the error side-effect,
                   ;; if `v` doesn't match the pattern
                   (term (#,(bspec/names-pattern-checker-name bs/n) ,v))])
            ;; call out to the metafunctions which we've given generated names
            (binding-object
             ;; destructure (note that this specifically does not build a new
             ;; binding object; this is the safe way of extracting subterms)
             (lambda ()
               (parameterize ([caching-enabled? #f]) ;; nondeterministic!
                 (match-define `(,destructured-v ,some-noop-subst)
                               (term (#,(bspec/names-freshener-name bs/n) ,v #t)))
                 destructured-v))
             ;; destructure/rec
             (lambda ()
               (parameterize ([caching-enabled? #f]) ;; nondeterministic!
                 (match-define `(,d/r-v ,subst)
                               (term (#,(bspec/names-freshener-name bs/n) ,v #f)))
                 ;; repack the binding object: its time has not yet come
                 `(,(make-binding-object d/r-v) ,subst)))

             ;; noop-binder-subst (returns a σ)
             (lambda ()
               (term (#,(bspec/names-noop-binder-subst-name bs/n) ,v)))
             ;; ref-rename
             (lambda (σ) (make-binding-object
                          (term (#,(bspec/names-r-renamer-name bs/n) ,σ ,v))
                          #f))
             ;; bnd-rename
             (lambda (σ) (make-binding-object
                          (#,(binder-renamer bs/n) σ v)
                          #f))))))
      make-binding-object))


(define (setup-binding-forms stx)
  (syntax-case stx ()
    [(setup-binding-forms binding-forms-stx lang-name)
     #`(begin . 
         #,(let loop ((bs/ns (parse-binding-forms #`binding-forms-stx #`lang-name)))
             (match bs/ns
                    [`((,bf-name ,bs/n) . ,rest)
                     #`(#,(freshener bs/n)
                        #,(noop-substituter bs/n)
                        #,(reference-renamer bs/n)
                        #,(binder-renamer bs/n)
                        #,(pattern-checker bs/n)
                        ;; TODO: do we really want the constructors to have the
                        ;; name of their binding form? It *is* sort of the
                        ;; obvious thing to do, however.
                        (define #,bf-name #,(binding-object-generator bs/n))
                        . #,(loop rest))]
                    [`() #`()])))]
    [_
     (raise-syntax-error
      'setup-binding-forms
      "Expected the syntax for some binding forms and the name of a language")]))


) ;; begin-for-syntax

;; === Runtime utility function ===

(define (assoc-shadow . lsts)
  (match lsts
    [`() `()]
    [`(,lst-primary . ,lst-rest)
     (append lst-primary
             (filter (lambda (elt) (not (assoc (car elt) lst-primary)))
                     (apply assoc-shadow lst-rest)))]))

;; Takes a redex value (an "expanded beta") with `shadow-sym`s, etc., and interprets it.
;; (Expaned betas are produced by `beta->subst-merger`).
;; Returns a substitution.
(define (interp-beta expanded-beta)
  (match expanded-beta
    [`(,first . ,rest)
     (cond [(eq? first shadow-sym) (apply assoc-shadow (map interp-beta rest))]
           [(eq? first rib-sym) (apply append (map interp-beta rest))]
           [else expanded-beta])] ;; we've hit a plain substitution
    [`() `()]
    [atom (redex-error #f "Unexpected term found in an expanded beta: ~s" atom)]))


;; TODO: worry about things like `(rib a_!_1)`






