#lang racket

(begin-for-syntax ;; this covers most of the file; let's not indent
 (require racket)
 (require trace)
(require (for-template "binding-objects.rkt"))
(require (for-template "reduction-semantics.rkt"))
(require (for-template (only-in "term.rkt" term)))
(require (for-template (only-in "matcher.rkt" caching-enabled?)))
(require (for-template "error.rkt"))
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
                    (generate-temporary (string-append str-name "-bnd-freshen"))
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
(struct bspec/names (bs lang-name freshener-name b-freshener-name
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

  ;; strip the extra stuff; generate a redex pattern that just matches
  ;; the 
  (define redex-pattern
    (let loop [(bpat body)]
      (match bpat
             [(import/internal bsub beta) (loop bsub)]
             [(list bsub ...) (map loop bsub)]
             [atom atom])))
  
  (define import-names (names-mentioned-in-bspec sbody))
  (define export-names (names-mentioned-in-beta export-beta))

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
         `((x) expr) 'nothing '(x) '() '(x)))
 
 (check-equal?
  (desyntax-bspec (surface-bspec->bspec
                   #'((a b (c d #:refers-to h e) #:refers-to (shadow e b (rib nothing))
                         f g h)
                      #:exports (rib e f))))
  (bspec `(a b ,(import/internal `(c ,(import/internal `d `h) e)
                                 `(shadow e b (rib nothing))) f g h)
         `(a b (c d e) f g h)
         `(rib e f) `(h e b) `(e f) `(h e b f)))



 ;; imported, exported, imported and exported
 (define ieie-bspec
   (surface-bspec->bspec
    #'((i e ie expr_1 #:refers-to (shadow ie i) expr_2 #:refers-to (shadow i ie))
       #:exports (shadow e ie))))

 (define ieie-bspec/names
   (bspec/names ieie-bspec #f #f #f #f #f #f))
 
 )


(define (boolify v)
  (if v #t #f))

(define (dedupe-names lst)
  (remove-duplicates lst bound-identifier=?))

(define (has-name? lst n)
  (memf (lambda (x) (bound-identifier=? x n)) lst))

(define (name-assoc n lst)
  (assf (lambda (x) (bound-identifier=? x n)) lst))

;; TODO: this is handling syntax; maybe it should be vanilla data?
(define (names-mentioned-in-beta beta)
  (dedupe-names (names-mentioned-in-beta/rec beta)))

(define (names-mentioned-in-beta/rec beta)
  (syntax-case beta (nothing)
    [nothing '()]
    [(op . betas)
     (append* (map names-mentioned-in-beta/rec (syntax->list #'betas)))]
    [name (list #'name)]))

;; TODO: this is handling surface bspecs; it should get normal bspecs
(define (names-mentioned-in-bspec/rec bspec)
  (syntax-case bspec ()
    [() '()]
    [(bspec-sub #:refers-to beta . rest)
     (append (names-mentioned-in-bspec/rec #'bspec-sub)
             (names-mentioned-in-beta #'beta)
             (names-mentioned-in-bspec/rec #'rest))]
    [(bspec-sub . rest)
     (append (names-mentioned-in-bspec/rec #'bspec-sub)
             (names-mentioned-in-bspec/rec #'rest))]
    [plain '()]))

(define (names-mentioned-in-bspec bspec)
  (dedupe-names (names-mentioned-in-bspec/rec bspec)))

(module+
 test

 (define (ds-lst lst) (map syntax->datum lst))
 
 (check-equal? (ds-lst (names-mentioned-in-beta #'a)) '(a))
 (check-equal? (ds-lst (names-mentioned-in-beta #'(shadow (rib a b c) (shadow b c d e)
                                                          (rib f nothing g h a a a) b
                                                          nothing nothing)))
               '(a b c d e f g h))

 (check-equal? (ds-lst (names-mentioned-in-bspec #'((x) e #:refers-to x))) '(x))
 (check-equal? (ds-lst (names-mentioned-in-bspec #'((x) e))) '())
 (check-equal? (ds-lst (names-mentioned-in-bspec #'(x_11
                                                    e_1 #:refers-to (shadow x_2 x_444)
                                                    (x_22 x_33 #:refers-to (rib x_1 x_2)
                                                          (e_2 e_3 #:refers-to (rib x_9))
                                                          #:refers-to x_3))))
               '(x_2 x_444 x_1 x_9 x_3))
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
  (define σ #`((variable_from variable_to) (... ...)))
  #`(define-metafunction #,(bspec/names-lang-name bs/n)
      [(#,(bspec/names-b-renamer-name bs/n)  #,σ
        (variable_binding-form-name . #,(bspec-redex-pattern bs)))
       (variable_binding-form-name . #,(binder-renamer-transcriber σ bs))]))



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
;; respects the beta's shadowing
;; (corresponds to 〚β〛(σ…) in the paper)
(define (beta->subst-merger beta map-of-renamings)
  (let loop ([beta beta])
    (syntax-case beta (shadow rib nothing)
      [nothing #`'()]
      ;; TODO: where do we check for erroneously-having-the-same-names-in-a-rib?
      [(rib) #`'()]
      [(rib sub-beta) (loop #`sub-beta)]
      [(rib sub-beta . sub-betas)
       #`(append #,(loop #`sub-beta)
                 #,(loop #`(rib . sub-betas)))]
      [(shadow) #`'()]
      [(shadow sub-beta) (loop #`sub-beta)]
      [(shadow sub-beta . sub-betas)
       #`(assoc-shadow #,(loop #`sub-beta)
                       #,(loop #`(shadow . sub-betas)))]
      [nt-ref (cadr (name-assoc #`nt-ref map-of-renamings))])))

(module+ test

  (check-equal?
   (syntax->datum (beta->subst-merger #'nothing '()))
   ''())
         
  ;; ideally, we'd do bound-identifier=?, but we're not worried about
  ;; that failure mode

  (check-equal?
   (syntax->datum
    (beta->subst-merger #'(rib (shadow (rib a b (rib) (shadow))
                                       (rib c d) nothing (shadow e f))
                               g h)
                        `((,#'a A) (,#'b B) (,#'c C) (,#'d D) (,#'e E) (,#'f F) (,#'g G) (,#'h H))))
   '(append (assoc-shadow (append A (append B (append '() '())))
                          (assoc-shadow
                           (append C D)
                           (assoc-shadow
                            '() (assoc-shadow E F))))
            (append G H))))




;; === Freshening ===
;; Motto: Freshen a binder iff it is exported to the top level, but no further.
;; Every import needs to be renamed according to the sets of binders it imports


;; bfreshening-info is an assoc:
;; (list (list identifier identifier-for-bfreshened-version renaming) ...)
;; exported-nts is a list of nonterminals
(define (bfreshener bfreshening-info exported-nts)
  (map
   (match-lambda
    [`(,mentioned-nt ,bfreshened ,vpat)
     #`(where (#,bfreshened #,vpat)
              ;; Is the name being exported to the top level?
              ,(if (xor #,(boolify (has-name? exported-nts mentioned-nt))
                        (term any_top-level?))
                   (destructure/rec (term #,mentioned-nt))
                   ;; If not, then the names are either free (and must not be
                   ;; renamed), or they will not become free by this destructuring
                   ;; (and thus don't need to be renamed)
                   (term (#,mentioned-nt ;; the value is not affected
                          ;; to participate in shadowing correctly
                          ;; without changing anything
                          ,(noop-binder-substitution (term #,mentioned-nt))))))])
   bfreshening-info))

(module+ test
 (check-equal? (map syntax->datum (bfreshener
                                   `((,#'b1 b1_ren σ_b1)
                                     (,#'b2 b2_ren σ_b2))
                                   `(,#'b1)))
               '((where (b1_ren σ_b1)
                        ,(if (xor #t (term any_top-level?))
                             (destructure/rec (term b1))
                             (term (b1 ,(noop-binder-substitution (term b1))))))
                 (where (b2_ren σ_b2)
                        ,(if (xor #f (term any_top-level?))
                             (destructure/rec (term b2))
                             (term (b2 ,(noop-binder-substitution (term b2)))))))))

;; TODO: when we rename binders, we also need to rename all names bound to them 
;; in the terms that export them!

(define (freshener bs/n)
  (define bs (bspec/names-bs bs/n))

  (define mentioned-nts (bspec-all-mentioned-nts bs))

  ;; An assoc mapping nonterminal references (that have been imported)
  ;; to their freshened version and to the names of the renamings that
  ;; need to be applied.
  ;; Complicating matters, we can't name the renaming as a whole
  ;; (we don't know what Redex language we're in), so we need to
  ;; call the renaming by a pattern like `((variable_from-98 variable_to-98) ...)' 
  (define bfreshening-info
    (map
     (lambda (mentioned-nt-stx)
       (define s (symbol->string (syntax->datum mentioned-nt-stx)))
       `(,mentioned-nt-stx
         ;; name for the result of freshening binders
         ;; (with the binders and all buried imports renamed)
         ,(generate-temporary (string-append s "_with-binders-freshened"))
         ,#`((#,(generate-temporary (string-append "variable_from" s))
              #,(generate-temporary (string-append "variable_to" s))) (... ...))))
     mentioned-nts))
 

  ;; will be spliced into (unquote ...)ed bits of the RHS; we need `term`
  (define renaming-substs/wrapped
    (map (match-lambda [`(,nt ,bfreshened ,r-pat)
                        `(,nt ,#`(term #,r-pat))])
         bfreshening-info))

  (define transcriber
    (let loop [(body (bspec-body bs))]
      (match body
        [`() #`()]
        [(import/internal body-sub beta)
         #`,(rename-references #,(beta->subst-merger beta renaming-substs/wrapped)
                               (term #,(loop body-sub)))]
        [`(,body-sub . ,rest-of-body)
         #`(#,(loop body-sub) . #,(loop rest-of-body))]
        [nt
         (match
          (name-assoc nt bfreshening-info)
          [`(,_ ,bfreshened-version-of-nt ,_) bfreshened-version-of-nt]
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
        , #,(beta->subst-merger (bspec-export-beta bs) renaming-substs/wrapped))
         ;; The necessary `where` clauses to generate the renamings that we'll use
       #,@(bfreshener bfreshening-info (bspec-exported-nts bs))])
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
              (term ,x-σ)
              (term
               (,uq (if (symbol? (term expr))
                        (term expr)
                        (first (destructure/rec (term expr)))))))))
       (,uq '()))
      (where (,x-bfreshened ,x-σ)
             (,uq (if (xor #f (term any_top-level?))
                      (destructure/rec (term x))
                      (term (x (,uq (noop-binder-substitution (term x))))))))]))
 
 (check-match
  (syntax->datum (freshener ieie-bspec/names))
  `(define-metafunction ,mf-name
     [(,_ (,bf-name ,i ,e ,ie ,expr_1 ,expr_2) any_top-level?)
      ((,bf-name
        ,i-ren
        ,e-ren
        ,ie-ren
        (,uq (rename-references
              (assoc-shadow (term ,ie-σ) (term ,i-σ)) ,_))
        (,uq (rename-references
              (assoc-shadow (term ,i-σ) (term ,ie-σ)) ,_)))
       (,uq (assoc-shadow (term ,e-σ) (term ,ie-σ))))
      (where (,ie-ren ,ie-σ) ,_)
      (where (,i-ren ,i-σ) ,_)
      (where (,e-ren ,e-σ) ,_)]))
 )

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
             ;; freshen binders (returns a σ)
             (lambda () 
               (parameterize ([caching-enabled? #f]) ;; nondeterministic!
                             (term (#,(bspec/names-b-freshener-name bs/n) ,v))))
             ;; ref-rename
             (lambda (σ) (make-binding-object
                          (term (#,(bspec/names-r-renamer-name bs/n) ,σ ,v))
                          #f))
             ;; bnd-rename
             (lambda (σ) (make-binding-object
                          (term (#,(bspec/names-b-renamer-name bs/n) ,σ ,v))
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
;; Now, we're in phase 0:

;; === Runtime utility functions ===

;; Turns a renaming into a no-op renaming that affects the same names.
;; Useful to "reserve" spots for names that are non-free, but imported
(define (smash-substitution σ)
  (map (lambda (pair) `(,(car pair) ,(car pair))) σ))


(define (assoc-shadow lst-primary lst-secondary)
  (append lst-primary
          (filter (lambda (elt) (not (assoc (car elt) lst-primary)))
                  lst-secondary)))


#| Sadly tests aren't available at this phase

 (module+ test
  (check-equal? (assoc-shadow '((a 1) (b 2) (c 3) (d 4))
                              '((e 5) (a 99) (b 999) (f 6) (g 7) (d 9999)))
                '((a 1) (b 2) (c 3) (d 4) (e 5) (f 6) (g 7))))
|#

;; TODO: worry about things like `(rib a_!_1)`






