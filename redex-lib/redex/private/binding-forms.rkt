#lang racket
(require "error.rkt")


(provide (for-syntax parse-binding-forms
                     freshener
                     reference-renamer
                     binder-renamer
                     setup-binding-forms
                     binding-object-generator))

;; this covers most of the file; let's not indent
(module binding-forms-for-syntax racket
;; the module is to make `module+ test` inside the `begin-for-syntax`
;; be located before the end of the file, so we can import it
(provide (all-defined-out))
        
(require "reduction-semantics.rkt")
        
;; == Runtime utility functions ==

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


;; These are to put markers inside Redex values
(define shadow-sym (gensym 'shadow))
(define rib-sym (gensym 'rib))


;; == phase 0 artifacts for tests that need to be referred to in phase 1 ==
(define-language lambda-calculus
  (expr (expr expr)
        (lambda (x) expr)
        x)
  (x variable-not-otherwise-mentioned))

(define-language ieie-lang
  ((i e ie expr)
   variable-not-otherwise-mentioned
   (i e ie expr expr)
   (list-o-refs variable-not-otherwise-mentioned ...)))

(define-language my-lambda-calc
   (e (e e)
      (my-lambda (x) e)
      x)
   (x variable-not-otherwise-mentioned))

(define-language let*-language
   (e (e e)
      (my-let* clauses e)
      x
      number)
   (x variable-not-otherwise-mentioned)
   (clauses (cl x e clauses)
            ()))


;; this also overs most of the file; we won't indent it either
(begin-for-syntax

(provide (all-defined-out))
 
(require racket)
(require (for-template "binding-objects.rkt"))
(require (for-template "reduction-semantics.rkt"))
(require (for-template (only-in "term.rkt" term)))
(require (for-template (only-in "matcher.rkt" caching-enabled?)))
(require (for-template "error.rkt"))
(require "error.rkt")
(require (only-in racket/syntax generate-temporary))



;; == Parsing and other general stuff ==

;; A binding-form is a feature of the language (e.g. `let`)
;; The only thing we need to know is how to construct one, so it's just a constructor
;; It takes a list of Redex terms and returns a binding-object

;; A binding-object is an opaque piece of syntax with binding information.
;; (see binding-objects.rkt)

(define-syntax (shadow stx) (raise-syntax-error 'shadow "used outside of binding specification"))
(define-syntax (rib stx) (raise-syntax-error 'rib "used outside of binding specification"))
(define-syntax (nothing stx) (raise-syntax-error 'nothing "used outside of binding specification"))

(struct import/internal (body beta) #:transparent)
(struct .../internal (body) #:transparent)

;; == Parsing ==

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
                   (surface-bspec->bspec #`(bf-body #:exports #,exports) lang-name))
             (parse-binding-forms rest-of-bfs lang-name)))]
    [() '()]
    [_ (raise-syntax-error 'define-language "expected a parenthesized binding form." #`anything)]))

(struct bspec
        (body redex-pattern export-beta imported-nts exported-nts
              all-mentioned-nts lang-name)
        #:transparent)

(define (surface-bspec->bspec surface-bspec lang-name)
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
      (syntax-case surface-bspec (...)
        [() bspec]
        [(#:refers-to . rest-of-body)
         (raise-syntax-error 'define-language
                             "#:refers-to requires an expression to its left"
                             #f surface-bspec)]
        [((... ...) . rest-of-body)
         (raise-syntax-error 'define-language
                             "... requires an expression to its left"
                             #f surface-bspec)]
        [(bspec-sub #:refers-to)
         (raise-syntax-error 'define-language
                             "#:refers-to requires an argument"
                             #f surface-bspec)]
        [(sbspec-sub #:refers-to imports-beta . rest-of-body)
         (loop #'rest-of-body
               (append bspec (list (import/internal (loop #'sbspec-sub '())
                                                    #'imports-beta))))]
        [(sbspec-sub (... ...) . rest-of-body)
         (loop #'rest-of-body
               (append bspec (list (.../internal (loop #'sbspec-sub '())))))]
        [(sbspec-sub . rest-of-body)
         (loop #'rest-of-body
               (append bspec (list (loop #'sbspec-sub '()))))]
        [atomic-pattern #'atomic-pattern])))

  ;; strip the extra import stuff; generate a plain redex pattern 
  (define redex-pattern
    (let loop [(bpat body)]
      (match bpat
        [(import/internal bsub beta) (loop bsub)]
        [`(,(.../internal bsub) . ,rest) `(,(loop bsub) ... . ,(loop rest))]
        [`(,bsub . ,rest)                `(,(loop bsub) . ,(loop rest))]
        [atom atom])))
  
  (define import-names (names-mentioned-in-bspec sbody))
  (define export-names (names-mentioned-in-beta export-beta 0))

  (bspec body redex-pattern export-beta import-names export-names
         (dedupe-names (append import-names export-names)) lang-name))

(module+ phase-1-test
 (require rackunit)
 (require "reduction-semantics.rkt")

 (define (ds s)
   (match s
          [`(,a . ,b) `(,(ds a) . ,(ds b))]
          [(import/internal p beta)
           (import/internal (ds p) (ds beta))]
          [(.../internal body) (.../internal (ds body))]
          [atomic (if (syntax? atomic)
                      (ds (syntax->datum atomic))
                      atomic)]))

 (define (ds-lst lst) (map (match-lambda [`(,x ,depth)
                                          `(,(syntax->datum x) ,depth)]) lst))
 
 (define (desyntax-bspec b)
   (match b
          [(bspec body pattern export i-names e-names all-names lang-name)
           (bspec (ds body) (ds pattern) (ds export) (ds i-names)
                  (ds e-names) (ds all-names) (ds lang-name))]))
 

 (define lambda-bspec
   (surface-bspec->bspec #'(((x) expr #:refers-to x) #:exports nothing)
                         #'lambda-calculus))
 ;; needed for the phase 0 tests
 (provide lambda-bspec)



 
 (check-equal?
  (desyntax-bspec lambda-bspec)
  (bspec `((x) ,(import/internal 'expr 'x))
         `((x) expr) 'nothing '((x 0)) '() '((x 0)) 'lambda-calculus))
 
 (check-equal?
  (desyntax-bspec (surface-bspec->bspec
                   #'((a b (c d #:refers-to h e) #:refers-to (shadow e b (rib nothing))
                         f g h)
                      #:exports (rib e f)) #'some-lang))
  (bspec `(a b ,(import/internal `(c ,(import/internal `d `h) e)
                                 `(shadow e b (rib nothing))) f g h)
         `(a b (c d e) f g h)
         `(rib e f) `((h 0) (e 0) (b 0)) `((e 0) (f 0)) `((h 0) (e 0) (b 0) (f 0))
         `some-lang))

 (define va-lambda-bspec
   (surface-bspec->bspec #`(((x (... ...)) expr #:refers-to (rib x (... ...)))
                            #:exports nothing) #`variable-arity-lambda-calc))

 

 (check-equal?
  (desyntax-bspec va-lambda-bspec)
  (bspec `((,(.../internal `x)) ,(import/internal `expr `(rib x ...)))
         `((x ...) expr) `nothing `((x 1)) `() `((x 1)) `variable-arity-lambda-calc))


 ;; imported, exported, imported and exported
 (define ieie-bspec
   (surface-bspec->bspec
    #`((i e ie expr_1 #:refers-to (shadow ie i) expr_2 #:refers-to (shadow i ie))
       #:exports (shadow e ie))  #`ieie-lang))
 
 (provide ieie-bspec)
 )


;; (handling `...` and outputting actual syntax is ugly; let's sequester it here)
;; transcribe-match : match the bspec-body of a bspec and generates a transcriber.
;; The transcriber generation has to be compositional; we do the recursion
;; for the user.
(define-syntax transcribe-match
  (syntax-rules (imp)
    [(transcribe-match bspec
       [(imp sub-body-done beta) handle-import/internal]
       [nt handle-nt])
     (let loop [(body (bspec-body bspec))
                (repeated-names (bspec-all-mentioned-nts bspec))]
       (match body
         [(import/internal sub-body beta)
          (define sub-body-done (loop sub-body repeated-names))
          handle-import/internal]
         
         ;; these cases are automatic; the user doesn't specify how they're done
         [(.../internal sub-body)
          (manual-... bspec sub-body repeated-names loop)]

         [`(,fst . ,rst) #`(#,(loop fst repeated-names) . #,(loop rst repeated-names))]
         [`() #`()]
 
         
         [nt handle-nt]))]))

;; We can't wrap `unquote`s in `...` with impunity, so we'll essentially
;; do MBE manually. We'll wrap a `...` around the names that drive the
;; repetition and feed them as arguments to a `map`.
(define (manual-... bspec transcribee repeated-names loop)
  (begin
    (define sub-repeated-names (repeated-names-in transcribee repeated-names))
    (define normal-args (generate-temporaries (map first sub-repeated-names)))
    ;; here's the `map` we're transcribing (unquoted out of a Redex term)
    #`,(map
        (lambda (#,@normal-args)
          ;; Oh, but we need to bind inside terms.
          ;; We'll shadow the name whose `...` we're handling
          ;; with the version that's one less `...`ed
          (redex-let #,(bspec-lang-name bspec)
            #,(map (lambda (s-r-n n-a)
                     #`[#,(first s-r-n) #,n-a]) ;; redex-let clause
                   sub-repeated-names normal-args)
            ;; append overrides in assocs
            (term #,(loop transcribee (append sub-repeated-names repeated-names)))))
        #,@(map (lambda (rep-name-and-depth)
                  #`(term (#,(first rep-name-and-depth) (... ...))))
                sub-repeated-names))))
    ;; `(... ...)` means "a plain `...` in the transcription output"    
   

;; returns all names with depth greater than 1, with their depths decremented
(define (repeated-names-in transcribee name-list)
  (match transcribee
    [(import/internal sub-body beta)
     ;; ignore the beta; allowing it to control repetition breaks the plain
     ;; redex-pattern
     (repeated-names-in sub-body name-list)]
    [(.../internal sub-body) (repeated-names-in sub-body name-list)]
    [(list elts ...)
     (dedupe-names
      (append* (map (lambda (e) (repeated-names-in e name-list)) elts)))]
    [nt (match (name-assoc nt name-list)
          [`(,_ ,0) `()]
          [`(,_ ,depth) `((,nt ,(- depth 1)))]
          [#f `()])]))

(module+ phase-1-test
 (check-equal?
  (ds-lst (repeated-names-in `(,#`a ,#`b ,#`c
                                    ,(.../internal
                                      (import/internal `(,#`d ,#`e) #`(rib f g h))))
                             `((,#`a 3) (,#`b 0) (,#`c 5) (,#`e 1) (,#`g 2))))
  `((a 2) (c 4) (e 0)))

 (check-match
  (syntax->datum (manual-... va-lambda-bspec #'x `((,#`x 1)) (lambda (x rn) x)))
  `(,uq (map
         (lambda (,x-normal)
           (redex-let variable-arity-lambda-calc
             ([x ,x-normal])
             (term x)))
         (term (x ,dotdotdot))))))




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


(define (has-name? lst n) 
  (memf (lambda (x) (bound-identifier=? (first x) n)) lst)) ;; second is the depth

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
 phase-1-test

 
 
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

;; == naive renaming operations ==


(define (reference-renamer-transcriber σ bs)
  (transcribe-match bs
    [(imp sub-body-done beta) sub-body-done]
    [atom (if (has-name? (bspec-all-mentioned-nts bs) atom)
              #`,(if (symbol? (term #,atom))
                     (term #,atom)
                     (rename-references (term #,σ) (term #,atom)))
              #`,(rename-references (term #,σ) (term #,atom)))]))

(define (reference-renamer bs σ-name v-name)
  ;; We want a Redex `...`, not a #` one
  (define σ-term #`((variable_from variable_to) (... ...)))

  #`(redex-let #,(bspec-lang-name bs)
      ([#,σ-term #,σ-name]
       [(variable_binding-form-name . #,(bspec-redex-pattern bs)) #,v-name])
    (term (variable_binding-form-name
           . #,(reference-renamer-transcriber σ-term bs)))))

(define (binder-renamer-transcriber σ bs)
  (transcribe-match bs
    [(imp sub-body-done beta) sub-body-done]
    [atom
     #`,(if (symbol? (term #,atom))
            #,(if (has-name? (bspec-all-mentioned-nts bs) atom)
                  #`(match (assoc (term #,atom) (term #,σ))
                           [`(,_ ,new-atom) new-atom]
                           [#f (term #,atom)])
                  #`(term #,atom))
            (rename-binders (term #,σ) (term #,atom)))]))

(define (binder-renamer bs σ-name v-name)
  ;; We want a Redex `...`, not a #` one
  (define σ-term #`((variable_from variable_to) (... ...)))

  #`(redex-let #,(bspec-lang-name bs)
      ([#,σ-term #,σ-name]
       [(variable_binding-form-name . #,(bspec-redex-pattern bs)) #,v-name])
      (term (variable_binding-form-name
             . #,(binder-renamer-transcriber σ-term bs)))))



(module+ phase-1-test
 (check-equal?
  (syntax->datum (reference-renamer-transcriber #'σ lambda-bspec))
  '((,(if (symbol? (term x)) (term x) (rename-references (term σ) (term x))))
     ,(rename-references (term σ) (term expr))))

 )

;; TODO: an old version of this also seemed to fire if the binding form doesn't match
;; the corresponding pattern in the language. Odd, but a probably a good feature.

;; expands to a procedure that errors if the given value doesn't match the pattern of the bspec
(define (pattern-checker bs)
  #`(term-match/single #,(bspec-lang-name bs)
      [(variable_binding-form-name . #,(bspec-redex-pattern bs)) #t]
      [any (redex-error 
            #f
            "cannot construct ~a; it does not match the pattern ~a from its binding spec"
            (term any) '(_ . #,(bspec-redex-pattern bs)))])
  )


;; == Beta handling ==

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

(module+ phase-1-test
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

 




;; == Freshening ==
;; Motto: Freshen a binder iff it is exported to the top level, but no further.
;; Every import needs to be renamed according to the sets of binders it imports


;; wrap a piece of syntax in the appropriate number of `...`s 
(define (wrap... stx depth)
  (if (= depth 0)
      stx
      #`(#,(wrap... stx (- depth 1)) (... ...))))

(define (wrap-map stx-fn stx-arg depth)
  (match depth
         [0 #`(#,stx-fn #,stx-arg)]
         [1 #`(map #,stx-fn #,stx-arg)]
         [_ #`(map (lambda (e) #,(wrap-map stx-fn #`e (- depth 1))) #,stx-arg)]))

;; exported-nts is a list of nonterminals
;; This returns a list of clauses for `redex-let*`.
(define (bfreshener renaming-info exported-nts top-level?-name)
  (map
   (match-lambda
    [`(,mentioned-nt ,bfreshened ,vpat ,depth)
     #`[#,(wrap... #`(#,bfreshened #,vpat) depth)
        ;; Is the name being exported to the top level?
        (if (xor #,(boolify (has-name? exported-nts mentioned-nt)) #,top-level?-name)
            #,(wrap-map #`destructure/rec #`(term #,(wrap... mentioned-nt depth)) depth)
            ;; If not, then the names are either free (and must not be
            ;; renamed), or they will not become free by this destructuring
            ;; (and thus don't need to be renamed)

            ;; to participate in shadowing correctly without changing anything
            #,(wrap-map #`noop-binder-substitution-plus-orig 
                        #`(term #,(wrap... mentioned-nt depth)) depth))]])
   renaming-info))

(module+ phase-1-test
         (check-equal?
          (map syntax->datum (bfreshener
                              `((,#'b1 b1_ren σ_b1 0)
                                (,#'b2 b2_ren σ_b2 0))
                              `((,#'b1 0))
                              #`tl?))
          '([(b1_ren σ_b1)
             (if (xor #t tl?)
                 (destructure/rec (term b1))
                 (noop-binder-substitution-plus-orig (term b1)))]
            [(b2_ren σ_b2)
             (if (xor #f tl?)
                 (destructure/rec (term b2))
                 (noop-binder-substitution-plus-orig (term b2)))]))

         (check-equal?
          (map syntax->datum (bfreshener
                              `((,#'b0 b0_ren σ_b0 0)
                                (,#'b1 b1_ren σ_b1 1)
                                (,#'b2 b2_ren σ_b2 2)
                                (,#'b3 b3_ren σ_b3 3))
                              `()
                              #`tl?))
          '([(b0_ren σ_b0)
             (if (xor #f tl?)
                 (destructure/rec (term b0))
                 (noop-binder-substitution-plus-orig (term b0)))]
            [((b1_ren σ_b1) ...)
             (if (xor #f tl?)
                 (map destructure/rec (term (b1 ...)))
                 (map noop-binder-substitution-plus-orig (term (b1 ...))))]
            [(((b2_ren σ_b2) ...) ...)
             (if (xor #f tl?)
                 (map (lambda (e) (map destructure/rec e)) (term ((b2 ...) ...)))
                 (map (lambda (e) (map noop-binder-substitution-plus-orig e)) 
                      (term ((b2 ...) ...))))]
            [((((b3_ren σ_b3) ...) ...) ...)
             (if (xor #f tl?)
                 (map (lambda (e) 
                        (map (lambda (e) (map destructure/rec e)) e)) (term (((b3 ...) ...) ...)))
                 (map (lambda (e) 
                        (map (lambda (e) (map noop-binder-substitution-plus-orig e)) e))
                      (term (((b3 ...) ...) ...))))]))
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

;; Emits syntax for a function that freshens values in accordance with the binding spec
;; The function takes a value and a boolean indicating whether we're "at" the top level
(define (freshener bs)

  ;; An assoc mapping nonterminal references (that have been imported)
  ;; to their freshened version and to the names of the renamings that
  ;; need to be applied.
  ;; Complicating matters, we can't name the renaming as a whole
  ;; (we don't know what Redex language we're in), so we need to
  ;; call the renaming by a pattern like `((variable_from-98 variable_to-98) ...)' 
  (define renaming-info (make-renaming-info (bspec-all-mentioned-nts bs)))
 
  (define transcriber
    (transcribe-match bs
      [(imp sub-body-done beta)
       #`,(rename-references #,(beta->subst-merger beta renaming-info)
                             (term #,sub-body-done))]
      [nt (match
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
                   (first (destructure/rec (term #,nt))))])]))
  
  #`(lambda (v top-level?)
      (redex-let* #,(bspec-lang-name bs)
        ;; define the renamings we'll use:
        ([(variable_binding-form-name . #,(bspec-redex-pattern bs)) v]
         #,@(bfreshener renaming-info (bspec-exported-nts bs) #`top-level?) )
        `(,(term (variable_binding-form-name . #,transcriber)) ;; new version of `v`
          , #,(beta->subst-merger (bspec-export-beta bs) renaming-info))))
  )


(module+ phase-1-test

         
 (define uq 'unquote) ;; oh boy
 ;; PS: wait a sec... match doesn't interpolate...
 
 (check-match
  (syntax->datum (freshener lambda-bspec))
  `(lambda (v top-level?)
     (redex-let* ,_ ([(,bf-name (x) expr) v]
                     [(,x-bfreshened ,x-σ)
                      (if (xor #f top-level?)
                          (destructure/rec (term x))
                          (noop-binder-substitution-plus-orig (term x)))])
       `((,uq (term (,bf-name
                     (,x-bfreshened)
                     (,uq (rename-references
                           (interp-beta (term ,x-σ))
                           (term
                            (,uq (if (symbol? (term expr))
                                     (term expr)
                                     (first (destructure/rec (term expr)))))))))))
         (,uq (interp-beta (term ())))))))

 (check-match
  (syntax->datum (freshener ieie-bspec))
  `(lambda (v top-level?)
     (redex-let* ,_ ([(,bf-name ,i ,e ,ie ,expr_1 ,expr_2) v]
                     [(,ie-ren ,ie-σ) ,_]
                     [(,i-ren ,i-σ) ,_] 
                     [(,e-ren ,e-σ) ,_])
       `((,uq (term (,bf-name
                     ,i-ren
                     ,e-ren
                     ,ie-ren
                     (,uq (rename-references
                           (interp-beta (term (,shad ,ie-σ ,i-σ))) ,_))
                     (,uq (rename-references
                           (interp-beta (term (,shad ,i-σ ,ie-σ))) ,_)))))
         (,uq (interp-beta (term (,shad ,e-σ ,ie-σ))))))))
 )

(define (noop-substituter bs)
  (define renaming-info (make-renaming-info (bspec-exported-nts bs)))

  (define σ-clauses
    (map
     (match-lambda
      [`(,nt ,_ ,σ ,depth)
       #`[#,(wrap... σ depth)
          (term #,(wrap... #` ,(noop-binder-substitution (term #,nt)) depth))]])
     renaming-info))

    #`(lambda (v)
        (redex-let* #,(bspec-lang-name bs)
                    ([(variable_binding-form-name . #,(bspec-redex-pattern bs)) v]
                     #,@σ-clauses)
                    #,(beta->subst-merger (bspec-export-beta bs) renaming-info))))

(module+ phase-1-test
 (check-match
  (syntax->datum (noop-substituter lambda-bspec))
  `(lambda (v) (redex-let* ,_
                 ([,bf v])
                 (interp-beta (term ()))))) ;; lambda doesn't export anything


 
 (check-match
  (syntax->datum (noop-substituter ieie-bspec))
  `(lambda (v) (redex-let* ,_
                 ([(,bf-name ,i ,e ,ie ,expr_1 ,expr_2) v]
                  [,e-σ (term (,uq (noop-binder-substitution (term ,e))))]
                  [,ie-σ (term (,uq (noop-binder-substitution (term ,ie))))])
                 (interp-beta (term (,shadow ,e-σ ,ie-σ)))))))


(module+ phase-1-test
 (define let*-clause-bspec
   (surface-bspec->bspec #'((x expr_val let*-clause_next #:refers-to x)
                            #:exports (shadow x let*-clause_next))
                         #'scheme))

 ;; TODO: check binder-freshening behavior
 )



;; == Tying everything together ==

(define (binding-object-generator bs)  
  #`(letrec
        ((make-binding-object
          ;; TODO: forbid `variable-prefix`, `side-condition`, and
          ;; plain symbols in binding patterns because (a) they're unnecessary
          ;; and (b) they could make `ref-rename` and `bnd-rename` generate
          ;; binding-objects that the metafunctions would fail to match on.
          (lambda (v [check-pattern? #t])
            (cond [check-pattern?
                   ;; do this for the error side-effect] if `v` doesn't match the pattern
                   (#,(pattern-checker bs) v)])
            ;; call out to the metafunctions which we've given generated names
            (binding-object
             ;; destructure (note that this specifically does not build a new
             ;; binding object; this is the safe way of extracting subterms)
             (lambda ()
               (match-define `(,destructured-v ,some-noop-subst) (#,(freshener bs) v #t))
               destructured-v)
             ;; destructure/rec
             (lambda ()
               (match-define `(,d/r-v ,subst) (#,(freshener bs) v #f))
               ;; repack the binding object: its time has not yet come
               `(,(make-binding-object d/r-v) ,subst))
             ;; noop-binder-subst (returns a σ)
             (lambda () (#,(noop-substituter bs) v))
             ;; noop-binder-subst-plus-orig (returns a pair the original value and a σ)
             (lambda () `(,v ,(#,(noop-substituter bs) v)))
             ;; ref-rename
             (lambda (σ) (make-binding-object #,(reference-renamer bs #`σ #`v) #f))
             ;; bnd-rename
             (lambda (σ) (make-binding-object #,(binder-renamer bs #`σ #`v) #f))))))
      make-binding-object))


(define (setup-binding-forms stx)
  (syntax-case stx ()
    [(setup-binding-forms binding-forms-stx lang-name)
     #`(begin . 
         #,(let loop ((bses (parse-binding-forms #`binding-forms-stx #`lang-name)))
             (match bses
                    [`((,bf-name ,bs) . ,rest)
                     #`(;; TODO: do we really want the constructors to have the
                        ;; name of their binding form? It *is* sort of the
                        ;; obvious thing to do, however.
                        (define #,bf-name #,(binding-object-generator bs))
                        . #,(loop rest))]
                    [`() #`()])))]
    [_
     (raise-syntax-error
      'setup-binding-forms
      "Expected the syntax for some binding forms and the name of a language")]))


) ;; begin-for-syntax
) ;; module binding-forms-for-syntax




(require 'binding-forms-for-syntax)
;; the `binding-forms-for-syntax` module only extisted to change the placement of
;; of the `phase-1-test` module and make it importable, so let's just
;; import everything here


;; == phase 0 tests ==

(module+ test
 ;; actually run the phase 1 tests, now that we're in the "real" test module
 (require (only-in (submod ".." binding-forms-for-syntax phase-1-test)))
         
 ;; also get some bspecs we'd like to reuse
 (require (for-syntax
           (only-in (submod ".." binding-forms-for-syntax phase-1-test)
                    lambda-bspec ieie-bspec)))

 (require rackunit) 
 (require "binding-objects.rkt")
 (require "reduction-semantics.rkt")


 ;; === fine-grained tests ===

 (define-syntax-rule (test-phase-1-fn (fn phase-0-args ...))
   (let-syntax
       ([test-phase-1-fn-helper
         (lambda (stx) (syntax-case stx ()
                         [(test-phase-1-fn) (fn phase-0-args ...)]))])
     (test-phase-1-fn-helper)))
 
 

 ;; ==== reference-renamer ====
 (check-equal?
  (test-phase-1-fn
   (reference-renamer lambda-bspec #``((x xx) (b bb) (c cc)) #``(lambda (x) (a b))))
  `(lambda (x) (a bb)))

 
 (check-equal?
  (test-phase-1-fn
   (reference-renamer ieie-bspec #``((a aa) (b bb) (c cc) (d dd) (e ee) (f ff))
                      #``(ieie a b c
                               (list-o-refs a b c d e f g)
                               (list-o-refs a b c d e f g))))
  `(ieie a b c (list-o-refs aa bb cc dd ee ff g) (list-o-refs aa bb cc dd ee ff g)))


 ;; ==== binder-renamer ====
 (check-equal?
  (test-phase-1-fn
   (binder-renamer lambda-bspec #``((x xx) (b bb) (c cc)) #``(lambda (x) (a b))))
  `(lambda (xx) (a b)))


 (check-equal?
  (test-phase-1-fn
   (binder-renamer ieie-bspec #``((a aa) (b bb) (c cc) (d dd) (e ee) (f ff))
                      #``(ieie a b c
                               (list-o-refs a b c d e f g)
                               (list-o-refs a b c d e f g))))
  `(ieie aa bb cc (list-o-refs a b c d e f g) (list-o-refs a b c d e f g)))

 ;; (need more tests here!)


 ;; ==== pattern-checker ====

 (check-exn exn:fail:redex? (lambda () ((test-phase-1-fn (pattern-checker lambda-bspec))
                                        `(lambda x x))))

 (check-not-exn (lambda () ((test-phase-1-fn (pattern-checker lambda-bspec))
                            `(lambda (x) x))))

 ;; ==== freshener ====

 (check-match
  ((test-phase-1-fn
    (freshener lambda-bspec))
   `(lambda (x) x) #t)
  `((lambda (,xx) ,xx) ())
  (not (equal? xx 'x)))

 )




(module+ test
 ;; === coarse-grained tests ===

 ;; This quick hack defines the necessary metafunctions,
 ;; and it defines a binding object construction function
 ;; for each binding form, naming it after that form.
 (define-syntax test-binding-forms setup-binding-forms)



 ;; So this defines `my-lambda` to be a binding constructor
 (test-binding-forms
  ((my-lambda (x) e #:refers-to x))
  my-lambda-calc)

 (define id (my-lambda '(my-lambda (x) x)))
 

 (check-match (destructure id)
              `(my-lambda (,x) ,x) ;; structure was preserved
              (not (eq? x 'x))) ;; we actually freshened the name
 
 ;; In addition to exports, this tests destructuring.
 ;; Being able to write `clauses` instead of `any` in the binding form definition
 ;; relies on `redex-match` being able to recognize the opaque binding object
 ;; as something that matches the pattern `(cl x e clauses)`.
 (test-binding-forms
  ((cl x e clauses #:refers-to x) #:exports (shadow clauses x)
   (my-let* clauses e #:refers-to clauses))

  let*-language)

 (define basic-clauses
   (cl `(cl a 4 ,(cl `(cl b (a 5) ,(cl `(cl c (b (a 6)) ())))))))
 
 (define basic-let* (my-let* `(my-let* ,basic-clauses (a (b c)))))


 (define (totally-destructure v)
   (match v
          [(binding-object destr _ _ _ _ _)
           (totally-destructure (destr))]
          [(list sub-v ...) (map totally-destructure sub-v)]
          [atom atom]))


 (check-match 
  (totally-destructure basic-let*)
  `(my-let* (cl ,a 4 (cl ,b (,a 5) (cl ,c (,b (,a 6)) ())))
            (,a (,b ,c))))

 ;; check that shadowing works properly
 (check-match
  (totally-destructure
   (my-let* `(my-let* ,(cl `(cl a 1 ,(cl `(cl a a ()))))
                      a)))
  `(my-let* (cl ,a 1 (cl ,b ,a ()))
            ,b)
  (not (equal? a b)))

 (define-language let3*-language
   (e (e e)
      x
      number
      (let3* ((x_a e_a) (x_b e_b) (x_c e_c)) e_body))
   (x variable-not-otherwise-mentioned))


 ;; a bigger, complexer form
 (test-binding-forms
  ((let3*
    ((x_a e_a) (x_b e_b #:refers-to x_a) (x_c e_c #:refers-to (shadow x_b x_a)))
    e_body #:refers-to (shadow x_c x_b x_a)))
  let3*-language)

 
 
 
 (check-match
  (totally-destructure
   (let3* `(let3* ((a 1) (b a) (c (a b)))
                  (a (b c)))))
  `(let3* ((,a 1) (,b ,a) (,c (,a ,b)))
          (,a (,b ,c))))


  ;; `...` in beta. Doesn't work yet
 (define-language variable-arity-lambda-calc
   (e (e e)
      (va-lambda (x ...) e)
      x)
   (x variable-not-otherwise-mentioned))

 (printf "<<<<<<~n~s~n>>>>>>>~n" (syntax->datum
           (expand-syntax-once #'(test-binding-forms
  ((va-lambda (x (... ...)) e #:refers-to (rib x (... ...))))
  variable-arity-lambda-calc) )))
 
 
 #;(test-binding-forms
  ((va-lambda (x ...) e #:refers-to (rib x ...)))
  variable-arity-lambda-calc)

 
 )
#;
(module+ test

 ;; === more fine-grained tests ===
 ;; (these depend on definitions from the coarse-grained tests)
 (define cl-bspec (surface-bspec->bspec
                   #'((cl x e clauses #:refers-to x) #:exports (shadow clauses x))))

 (define cl-bspec/names (bspec/names cl-bspec #`let*-language 0 0 0 0 0))

 (define my-let*-bspec (surface-bspec->bspec
                        #'((my-let* clauses e #:refers-to clauses)) #`let*-language))


 
 ;; We really need to test whether binder-renamer works correctly on
 ;; exported and non-exported binders of child nodes
 (check-equal?
  (test-phase-1-fn
   (binder-renamer cl-bspec #``((a aa) (c cc)) #`basic-clauses))
  (cl `(cl aa 4 ,(cl `(cl b (a 5) ,(cl `(cl cc (b (a 6)) ())))))))
)





;; TODO: worry about things like `(rib a_!_1)`







