#lang racket
(require "binding-objects.rkt")
(require rackunit)
(require (only-in racket/syntax generate-temporary))


(provide parse-binding-forms ;; just for testing
         compile-binding-forms)

;; hash-table is a hasheq from symbol to binding-form

;; A binding-form is, e.g., `let`, a feature of the language.
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
(define (parse-binding-forms binding-forms-stx)
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
                                            #f #'rest-plus-exports)]
           [(rest-of-bfs ...)
            (values #'(rest-of-bfs ...) #'nothing)]))

       (define str-name (symbol->string (syntax->datum #'bf-name)))

       (cons (list #'bf-name (bspec/names
                              (surface-bspec->bspec #`(bf-body #:exports #,exports))
                              #`TODO
                              (generate-temporary (string-append str-name "-freshen"))
                              (generate-temporary (string-append str-name "-ref-ren"))
                              (generate-temporary (string-append str-name "-bnd-ren"))))
             (parse-binding-forms rest-of-bfs)))]
    [() '()]))

(struct bspec
        (body redex-pattern export-beta imported-nts exported-nts all-mentioned-nts)
        #:transparent)

;; this has the names of the redex metafunctions we generate, and the language, too
(struct bspec/names (bs lang-name freshener-name r-renamer-name b-renamer-name)
        #:transparent)

(define (surface-bspec->bspec surface-bspec)
  (define-values (sbody export-beta)
    (syntax-case surface-bspec () [(b #:exports e) (values #'b #'e)]))

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

(module+
 test

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


 )


(define (dedupe-names lst)
  (remove-duplicates lst bound-identifier=?))

(define (has-name? lst n)
  (memf (lambda (x) (bound-identifier=? x n)) lst))

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


;; === Renaming ===

(define (rename-references σ v)
  (match v
         [(list sub-v ...) (map (lambda (x) (rename-references σ x)) sub-v)]
         ;; TODO: identify binding objects and reference-rename them
         [(? symbol? s)
          (match (assoc s σ)
                 [`(,_ ,new-s) new-s]
                 [#f s])]))

(define (rename-binders σ v)
  (match v
         [(list sub-v ...) (map (lambda (x) (rename-binders σ x)) sub-v)]
         ;; TODO: identify binding objects and binder-rename them
         [(? symbol? s)
          (match (assoc s σ)
                 [`(,_ ,new-s) new-s]
                 [#f s])]))

(module+
 test
 (define σ '((a aa) (s ss) (h hh)))
 
 (check-equal? (rename-references σ
                                  '(t h i (s i s (a (t) e) s) t))
               '(t hh i (ss i ss (aa (t) e) ss) t))
 
 )


(define (reference-renamer-transcriber bs σ)
  (let loop [(body (bspec-body bs))]
    (match body
           [(import/internal sub-body beta) (loop sub-body)]
           [(list sub-body ...) (datum->syntax #f (map loop sub-body))]
           [atom
            (if (has-name? (bspec-all-mentioned-nts bs) atom)
                #`,(if (symbol? (term #,atom))
                        (term #,atom)
                        (rename-references #,σ (term #,atom)))
                #`,(rename-references #,σ (term #,atom)))])))

(define (reference-renamer bs renamer-name language-name)
  ;; We want a Redex `...`, not a #` one
  (define σ #`((variable_from variable_to) (... ...)))
  #`(define-metafunction #,language-name
      [(#,renamer-name (variable_binding-form-name . #,(bspec-redex-pattern bs)) #,σ)
       (variable_binding-form-name . #,(reference-renamer-transcriber bs σ))]))


(define (binder-renamer-transcriber bs σ)
  (let loop [(body (bspec-body bs))]
    (match body
           [(import/internal sub-body beta) (loop sub-body)]
           [(list sub-body ...) (datum->syntax #f (map loop sub-body))]
           [atom
            (if (has-name? (bspec-all-mentioned-nts bs) atom)
                #`,(if (symbol? (term #,atom))
                       (rename-binders #,σ (term #,atom))
                       (term #,atom))
                atom)])))

(module+ test
 (check-equal?
  (syntax->datum (reference-renamer-transcriber
                  (surface-bspec->bspec
                   #'(((x) e #:refers-to x) #:exports nothing)) #'σ))
  '((,(if (symbol? (term x)) (term x) (rename-references σ (term x))))
     ,(rename-references σ (term e)))))

;; === Beta handling ===
(define (assoc-shadow lst-primary lst-secondary)
  (append lst-primary
          (filter (lambda (elt) (not (assoc (car elt) lst-primary)))
                  lst-secondary)))


(module+ test
 (check-equal? (assoc-shadow '((a 1) (b 2) (c 3) (d 4))
                             '((e 5) (a 99) (b 999) (f 6) (g 7) (d 9999)))
               '((a 1) (b 2) (c 3) (d 4) (e 5) (f 6) (g 7))))

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
      [nt-ref (cadr (assoc (syntax->datum #`nt-ref) map-of-renamings))])))

(module+ test

  ;; ideally, we'd do bound-identifier=?, but we're not worried about
  ;; that failure mode

  (check-equal?
   (syntax->datum
    (beta->subst-merger #'(rib (shadow (rib a b (rib) (shadow))
                                       (rib c d) nothing (shadow e f))
                               g h)
                        '((a A) (b B) (c C) (d D) (e E) (f F) (g G) (h H))))
   '(append (assoc-shadow (append A (append B (append '() '())))
                          (assoc-shadow
                           (append C D)
                           (assoc-shadow
                            '() (assoc-shadow E F))))
            (append G H))))




;; === Freshening ===

(define (freshener bs)
  ;; An assoc mapping nonterminal references (that have been imported)
  ;; to the names of the renamings that need to be applied.
  ;; Complicating matters, we can't name the renaming as a whole
  ;; (we don't know what Redex language we're in), so we need to
  ;; call the renaming by a pattern like
  ;; `((variable_from-98 variable_to-98) ...)' 
  (define renaming-pats
    (map (lambda (imported-nt-stx)
           (define s (symbol->string (syntax->datum imported-nt-stx)))
           `(,(syntax->datum imported-nt-stx)
             ,#`((#,(generate-temporary (string-append "variable_from" s))
                  #,(generate-temporary (string-append "variable_to" s))) (... ...))))
         (bspec-imported-nts bs)))

  ;; The necessary `where` clauses to generate the renamings that we'll use
  (define renamings
    (map (match-lambda
          [`(,imported-nt ,vpat)
           #`(where #,vpat ,(freshen-binders (term #,imported-nt)))])
         renaming-pats))

  (define transcriber
    (let loop [(body (bspec-body bs))]
      (match body
        [`() #`()]
        [(import/internal body-sub beta)
         #`,(rename-references (term #,(beta->subst-merger beta renaming-pats))
                               (term #,(loop body-sub)))]
        [`(,body-sub . ,rest-of-body)
         #`(#,(loop body-sub) . #,(loop rest-of-body))]
        [atom
         (match (assoc (syntax->datum atom) renaming-pats)
           [`(,_ ,renaming-pat)
            #`,(rename-binders (term #,renaming-pat) (term #,atom))]
           [#f
            (if (has-name? (bspec-exported-nts bs) atom)
                #`(term #,atom)
                ;; names that aren't imported or exported are references
                #`,(if (symbol? (term #,atom)) 
                       (term #,atom)
                       ;; TODO: this minor corner case might slow things down.
                       ;; Suggested optimization: bail out early in the very
                       ;; common case where #,atom exports nothing.
                       ;; 
                       ;; What's going on here is that, if an nt has free binders,
                       ;; but doesn't get imported or exported, they still need to
                       ;; be freshened. (effectively, they're imported into zero places)
                       ;; It's a shame, binders that don't get imported/exported
                       ;; have no use at all! But our clients might implement
                       ;; a perfectly reasonable language, which their clients
                       ;; will use in this way, so it should work right.
                       (rename-binders (freshen-binders (term #,atom))
                                       (term #,atom))))])])))

  #`(define-metafunction TODO-LANG-NAME
      [(TODO-FRESHEN-NAME (variable_binding-form-name . #,(bspec-redex-pattern bs)))
       (variable_binding-form-name . #,transcriber)
       #,@renamings])
  )

(module+ test
         
 (define uq 'unquote) ;; oh boy
         
 (check-match
  (syntax->datum (freshener lambda-bspec))
  `(define-metafunction ,_
     [(,_ (,bf-name (x) expr))
      (,bf-name
       ((,uq (rename-binders (term ,x-σ) (term x))))
       (,uq (rename-references
             (term ,x-σ)
             (term
              (,uq (if (symbol? (term expr))
                       (term expr)
                       (rename-binders (freshen-binders (term expr)) (term expr))))))))
      (where ,x-σ
             (,uq (freshen-binders (term x))))])))






 ;; we might not need to parse betas; aren't they already in a good form?

#;(struct shadow (beta))

#;(define (parse-beta beta-stx)
  (syntax-case beta-stx (shadow rib nothing) ;; PS: maybe these should be syntax nonces
    [(shadow beta ...)
     
     ]))


(define (compile-binding-forms binding-forms-stx)
  (define bf-assoc (parse-binding-forms binding-forms-stx))

  ;; PS: actually compile here (need to figure out how to handle procedures.
  ;; In particular, we need to do a matching that knows that `a_!_1` and
  ;; another `a_!_1` are not the same name. We could special-case that out, since
  ;; `_!_` is clearly wrong in a reference to a value anyways, but that sounds
  ;; fragile)
  
  (make-hasheq bf-assoc))


