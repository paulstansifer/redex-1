#lang racket
(require "error.rkt")


(provide (for-syntax parse-binding-forms
                     freshener
                     reference-renamer
                     binder-renamer))

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


(struct language-functions (freshen/rec noop-bind-subst ref-rename bnd-rename))

(define cur-language-fns (make-parameter #f))

;; These functions go through the parameter `cur-language-fns` to to get
;; the binding-form-dispatching behvior we want

(define (freshen/rec v)
  ((language-functions-freshen/rec (cur-language-fns)) v))

(define (noop-binder-substitution v)
  ((language-functions-noop-bind-subst (cur-language-fns)) v))

(define (noop-binder-substitution-plus-orig v)
  `(,v ,((language-functions-noop-bind-subst (cur-language-fns)) v)))

(define (rename-references σ v)
  ((language-functions-ref-rename (cur-language-fns)) σ v))

(define (rename-binders σ v)
  ((language-functions-bnd-rename (cur-language-fns)) σ v))


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
(require (for-template "reduction-semantics.rkt"))
(require (for-template (only-in "term.rkt" term)))
(require (for-template (only-in "matcher.rkt" caching-enabled?)))
(require (for-template "error.rkt"))
(require "error.rkt")
(require (only-in racket/syntax generate-temporary))



;; == Parsing and other general stuff ==


(define-syntax (shadow stx) (raise-syntax-error 'shadow "used outside of binding specification"))
(define-syntax (rib stx) (raise-syntax-error 'rib "used outside of binding specification"))
(define-syntax (nothing stx) (raise-syntax-error 'nothing "used outside of binding specification"))

(struct import/internal (body beta) #:transparent)
(struct .../internal (body) #:transparent)

;; == Parsing ==

;; takes the syntax that comes after a `#:binding-forms` and returns a
;; list of `bspec`s
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

       (cons (surface-bspec->bspec #`(bf-body #:exports #,exports) lang-name #'bf-name)
             (parse-binding-forms rest-of-bfs lang-name)))]
    [() '()]
    [anything (raise-syntax-error 'define-language "expected a parenthesized binding form." #`anything)]))


;; body: a tree, with `import/internal`s, `.../internal`s, and identifiers,
;;       representing the binding strucutre
;; redex-pattern: a pattern, ready for matching in redex, that has all the binding
;;       information strupped out. Unlike body, it also includes the binding form name
;; export-beta: a beta indicating what `nt`s get exported
(struct bspec
        (body redex-pattern export-beta imported-nts exported-nts
              ported-nts lang-name)
        #:transparent)

(define (surface-bspec->bspec surface-bspec lang-name bf-name)
  (define-values (sbody export-beta)
    (syntax-case surface-bspec ()
      [(b #:exports e) (values #'b #'e)]
      [_ (raise-syntax-error 'surface-bspec->bspec "expected `(body #:exports beta)`"
                             surface-bspec)]))

  ;; replaces `#:refers-to` with an easier-to-maniuplate syntax
  (define body
    `(,bf-name
      . ,(let loop [(surface-bspec sbody)
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
             [atomic-pattern #'atomic-pattern]))))

  ;; strip the extra import stuff; generate a plain redex pattern 
  (define redex-pattern
    (let loop [(bpat body)]
      (match bpat
             [(import/internal bsub beta) (loop bsub)]
             [`(,(.../internal bsub) . ,rest) `(,(loop bsub) ... . ,(loop rest))]
             [`(,bsub . ,rest)                `(,(loop bsub) . ,(loop rest))]
             [atom atom])))
   
  (define import-names (names-imported-in-bspec sbody))
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
                         #'lambda-calculus #'lambda))



 
 (check-equal?
  (desyntax-bspec lambda-bspec)
  (bspec `(lambda (x) ,(import/internal 'expr 'x))
         `(lambda (x) expr) 'nothing '((x 0)) '() '((x 0)) 'lambda-calculus))
 
 (check-equal?
  (desyntax-bspec (surface-bspec->bspec
                   #'((a b (c d #:refers-to h e) #:refers-to (shadow e b (rib nothing))
                         f g h)
                      #:exports (rib e f)) #'some-lang #'form))
  (bspec `(form a b ,(import/internal `(c ,(import/internal `d `h) e)
                                 `(shadow e b (rib nothing))) f g h)
         `(form a b (c d e) f g h)
         `(rib e f) `((h 0) (e 0) (b 0)) `((e 0) (f 0)) `((h 0) (e 0) (b 0) (f 0))
         `some-lang))

 (define va-lambda-bspec
   (surface-bspec->bspec #`(((x (... ...)) expr #:refers-to (rib x (... ...)))
                            #:exports nothing) #`variable-arity-lambda-calc
                            #`va-lambda))

 

 (check-equal?
  (desyntax-bspec va-lambda-bspec)
  (bspec `(va-lambda (,(.../internal `x)) ,(import/internal `expr `(rib x ...)))
         `(va-lambda (x ...) expr) `nothing `((x 1)) `() `((x 1))
         `variable-arity-lambda-calc))


 ;; imported, exported, imported and exported
 (define ieie-bspec
   (surface-bspec->bspec
    #`((i e ie expr_1 #:refers-to (shadow ie i) expr_2 #:refers-to (shadow i ie))
       #:exports (shadow e ie))  #`ieie-lang #`ieie))
 
 )


;; (handling `...` and outputting actual syntax is ugly; let's sequester it here)
;; transcribe-match : match the bspec-body of a bspec and generates a transcriber.
;; The transcriber generation has to be compositional; we do the recursion
;; for the user.
(define-syntax transcribe-match
  (syntax-rules (imp)
    [(transcribe-match bspec extra-repeated-names
       [(imp sub-body-done beta) handle-import/internal]
       [nt handle-nt])
     (let ([transcriber-with-.../internal
            ;; don't touch the head of the form
            ;; (I'm unsure what happens if we do allow it to be renamed...)
            (let loop [(body (rest (bspec-body bspec)))]
              (match body
                     [(import/internal sub-body beta)
                      (define sub-body-done (loop sub-body))
                      handle-import/internal]
                     
                     ;; these three cases are automatic; the user doesn't specify how they're done
                     [(.../internal sub-body) (.../internal (loop sub-body))]
                     [`(,fst . ,rst) #`(#,(loop fst) . #,(loop rst))]
                     [`() #`()]
                     
                     [nt handle-nt]))])
       
       ;; transcriber-with-.../internal is syntax, except that it has
       ;; occasional `.../internal`s, so let's handle them now (we had to
       ;; wait so that we could examine the *actual* names we'd be ...ing over)
       (define transcriber-with-working-repetitions
         (let loop [(body transcriber-with-.../internal)
                    (repeated-names
                     (append extra-repeated-names
                             (names-mentioned-in (bspec-body bspec))))]
           (syntax-case body ()
             [(fst . rst)
              #`(#,(loop #`fst repeated-names) . #,(loop #`rst repeated-names))]
             [() #`()]
             [single (if (.../internal? (syntax-e #`single))
                         (manual-... bspec (.../internal-body (syntax-e #`single))
                                     repeated-names loop)
                         #`single)])))       
      
       #`(term (#,(first (bspec-body bspec))
                . #,transcriber-with-working-repetitions)))]))

;; This is a lot like names-imported-in-bspec, but the latter only looks at names
;; mentioned in `refers-to`s.

(define (names-mentioned-in/rec body depth)
  (match body
         [(import/internal sub-body beta) 
          (append (names-mentioned-in/rec sub-body depth)
                  (names-mentioned-in-beta beta depth))]
         [(.../internal sub-body) (names-mentioned-in/rec sub-body (+ depth 1))]
         [`(,fst . ,rst) (append (names-mentioned-in/rec fst depth)
                                 (names-mentioned-in/rec rst depth))]
         [`() `()]
         [(? identifier? ident) `((,ident ,depth))]
         [_ `()]))

(define (names-mentioned-in body)
  (dedupe-names (names-mentioned-in/rec body 0)))


(define (override-name-list overrider old-list)
  (append overrider
          (filter (match-lambda [`(,nt ,_) (not (has-name? overrider nt))])
                  old-list)))

;; wrap a piece of syntax in the appropriate number of `...`s 
(define (wrap... stx depth)
  (if (= depth 0)
      stx
      #`(#,(wrap... stx (- depth 1)) (... ...))))
;; `(... ...)` means "a plain `...` in the transcription output" 


;; We can't wrap `unquote`s in `...` with impunity, so we'll essentially
;; do MBE manually. We'll wrap a `...` around the names that drive the
;; repetition and feed them as arguments to a `map`.
;; We thread `loop` through this so that we can reduce the count of the
;; remaining number of `...`s we need to wrap around the names we've just wrapped
(define (manual-... bspec almost-transcriber repeated-names loop)
  (begin
    (define sub-repeated-names (repeated-names-in almost-transcriber repeated-names))
    (define normal-args (generate-temporaries (map first sub-repeated-names)))
    ;; here's the `map` we're transcribing (unquoted out of a Redex term)
    #`,@(map
         (lambda (#,@normal-args)
           ;; Oh, but we need to bind inside terms.
           ;; We'll shadow the name whose `...` we're handling
           ;; with the version that's one less `...`ed
           (redex-let #,(bspec-lang-name bspec)
                      #,(map (match-lambda* 
                              [`((,rep-name ,depth) ,n-a)
                               #`[#,(wrap... rep-name depth) #,n-a]]) ;; redex-let clause
                             sub-repeated-names normal-args)
                      (term #,(loop almost-transcriber 
                                    (override-name-list
                                     sub-repeated-names repeated-names)))))
         #,@(map (match-lambda [`(,rep-name ,depth)
                                #`(term #,(wrap... rep-name (+ depth 1)))])
                 sub-repeated-names))))

   

;; returns all names with depth greater than 1, with their depths decremented
(define (repeated-names-in almost-transcriber name-list)
  (syntax-case almost-transcriber (rename-references)
    [(fst . rst)
     (dedupe-names (append (repeated-names-in #`fst name-list)
                           (repeated-names-in #`rst name-list)))]
    [() `()]
    [single
     (match (syntax-e #`single)
            [(.../internal body) (repeated-names-in body name-list)]
            [(? symbol?) ;; it was an identifier
             (match (name-assoc #`single name-list)
                [`(,_ ,0) `()]
                [`(,nt ,depth) `((,nt ,(- depth 1)))]
                [#f `()])]
            [_ `()])]))

(module+ phase-1-test
 (check-equal?
  (ds-lst (repeated-names-in #`(a b c
                                 #,(.../internal
                                     #`(rename-references (rib f g h) (d e) )))
                             `((,#`a 3) (,#`b 0) (,#`c 5) (,#`e 1) (,#`g 2))))
  `((a 2) (c 4) (g 1) (e 0)))

 (check-match
  (syntax->datum (manual-... va-lambda-bspec #'x `((,#`x 1)) (lambda (x rn) x)))
  `(,uqs (map
          (lambda (,x-normal)
            (redex-let variable-arity-lambda-calc
              ([x ,x-normal])
              (term x)))
          (term (x ,dotdotdot)))))


 (check-match
  (syntax->datum (manual-... va-lambda-bspec #`(x (y)) `((,#`x 1) (,#`y 1))
                             (lambda (x rn) x)))
  `(,uqs (map
          (lambda (,x-normal ,y-normal)
            (redex-let variable-arity-lambda-calc
              ([x ,x-normal] [y ,y-normal])
              (term (x (y)))))
          (term (x ,dotdotdot)) (term (y ,dotdotdot)))))

 )





(define (name-assoc n lst)
  (assf (lambda (x) (bound-identifier=? x n)) lst))

(define (boolify v)
  (if v #t #f))


;; When these functions talk about lists of names, they mean assocs
;; from names to numbers (the number being how many `...`s the name is underneath)

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
;; Names mentioned by some beta #:referred-to in the bspec
(define (names-imported-in-bspec/rec bspec depth)
  (syntax-case bspec (...)
    [() '()]
    [(bspec-sub (... ...) . rest)
     (append (names-imported-in-bspec/rec #'bspec-sub (+ depth 1))
             (names-imported-in-bspec/rec #'rest depth))]
    [(bspec-sub #:refers-to beta (... ...) . rest)
     (append (names-imported-in-bspec/rec #'bspec-sub (+ depth 1))
             (names-mentioned-in-beta #'beta (+ depth 1))
             (names-imported-in-bspec/rec #'rest depth))]
    [(bspec-sub #:refers-to beta . rest)
     (append (names-imported-in-bspec/rec #'bspec-sub depth)
             (names-mentioned-in-beta #'beta depth)
             (names-imported-in-bspec/rec #'rest depth))]
    [(bspec-sub . rest)
     (append (names-imported-in-bspec/rec #'bspec-sub depth)
             (names-imported-in-bspec/rec #'rest depth))]
    [plain '()]))

(define (names-imported-in-bspec bspec)
  (dedupe-names (names-imported-in-bspec/rec bspec 0)))


(module+
 phase-1-test

 
 
 (check-equal? (ds-lst (names-mentioned-in-beta #`a 0)) `((a 0)))
 (check-equal? (ds-lst (names-mentioned-in-beta #`(shadow (rib a b c) (shadow b c d e)
                                                          (rib f nothing g h a a a) b
                                                          nothing nothing) 0))
               (map (lambda (x) `(,x 0)) `(a b c d e f g h)))

 (check-equal? (ds-lst (names-imported-in-bspec #`((x) e #:refers-to x))) `((x 0)))
 (check-equal? (ds-lst (names-imported-in-bspec #`((x) e))) `())
 (check-equal? (ds-lst (names-imported-in-bspec #`(x_11
                                                    e_1 #:refers-to (shadow x_2 x_444)
                                                    (x_22 x_33 #:refers-to (rib x_1 x_2)
                                                          (e_2 e_3 #:refers-to (rib x_9))
                                                          #:refers-to x_3))))
               (map (lambda (x) `(,x 0)) `(x_2 x_444 x_1 x_9 x_3)))
 )

;; == naive renaming operations ==
;; TODO: make these un-naive; naive reference/binder renaming breaks alpha-equivalence

(define (reference-renamer bs σ-name)
  (transcribe-match bs '()
    [(imp sub-body-done beta) sub-body-done]
    [atom (if (has-name? (bspec-ported-nts bs) atom)
              #` ,(if (symbol? (term #,atom))
                      (term #,atom)
                      (rename-references #,σ-name (term #,atom)))
              #` ,(rename-references #,σ-name (term #,atom)))]))


(define (vanilla-reference-renamer σ-name)
  `(, #`[(any (... ...))
         (map (lambda (elt) (rename-references #,σ-name elt))
              (term (any (... ...))))]
    , #`[variable
         (match (assoc (term variable) #,σ-name)
           [`(,_ ,new-s) new-s]
           [#f (term variable)])]
    , #`[any (term any)]))

(define (binder-renamer bs σ-name)
  (transcribe-match bs '()
    [(imp sub-body-done beta) sub-body-done]
    [atom
     #` ,(if (symbol? (term #,atom))
             #,(if (has-name? (bspec-ported-nts bs) atom)
                   #`(match (assoc (term #,atom) #,σ-name)
                            [`(,_ ,new-atom) new-atom]
                            [#f (term #,atom)])
                   #`(term #,atom))
             (rename-binders #,σ-name (term #,atom)))]))


(define (vanilla-binder-renamer σ-name)
  `(, #`[(any (... ...)) (map (lambda (elt) (rename-binders #,σ-name elt))
                              (term (any (... ...))))]
    ;; symbols should only be renamed if mentioned, and nothing
    ;; is mentioned outside of binding forms
    , #`[any (term any)]))


(module+ phase-1-test
 (check-equal?
  (syntax->datum (reference-renamer lambda-bspec #`σ))
  '(term (lambda (,(if (symbol? (term x)) (term x) (rename-references σ (term x))))
     ,(rename-references σ (term expr)))))

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
    [`(,ported-nt ,bfreshened ,vpat ,depth)
     #`[#,(wrap... #`(#,bfreshened #,vpat) depth)
        ;; Is the name being exported to the top level?
        (if (xor #,(boolify (has-name? exported-nts ported-nt)) #,top-level?-name)
            #,(wrap-map #`freshen/rec #`(term #,(wrap... ported-nt depth)) depth)
            ;; If not, then the names are either free (and must not be
            ;; renamed), or they will not become free by this destructuring
            ;; (and thus don't need to be renamed)

            ;; to participate in shadowing correctly without changing anything
            #,(wrap-map #`noop-binder-substitution-plus-orig 
                        #`(term #,(wrap... ported-nt depth)) depth))]])
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
                 (freshen/rec (term b1))
                 (noop-binder-substitution-plus-orig (term b1)))]
            [(b2_ren σ_b2)
             (if (xor #f tl?)
                 (freshen/rec (term b2))
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
                 (freshen/rec (term b0))
                 (noop-binder-substitution-plus-orig (term b0)))]
            [((b1_ren σ_b1) ...)
             (if (xor #f tl?)
                 (map freshen/rec (term (b1 ...)))
                 (map noop-binder-substitution-plus-orig (term (b1 ...))))]
            [(((b2_ren σ_b2) ...) ...)
             (if (xor #f tl?)
                 (map (lambda (e) (map freshen/rec e)) (term ((b2 ...) ...)))
                 (map (lambda (e) (map noop-binder-substitution-plus-orig e)) 
                      (term ((b2 ...) ...))))]
            [((((b3_ren σ_b3) ...) ...) ...)
             (if (xor #f tl?)
                 (map (lambda (e) 
                        (map (lambda (e) (map freshen/rec e)) e)) (term (((b3 ...) ...) ...)))
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
(define (make-renaming-info ported-nts)
  (map
   (match-lambda
    [`(,ported-nt-stx ,depth)
     (define s (symbol->string (syntax->datum ported-nt-stx)))
     `(,ported-nt-stx
       ;; name for the result of freshening binders
       ;; (with the binders and all buried imports renamed)
       ,(generate-temporary (string-append s "_with-binders-freshened"))
       ,#`((#,(generate-temporary (string-append "variable_from" s))
            #,(generate-temporary (string-append "variable_to" s))) (... ...))
       ,depth)])
   ported-nts))

;; TODO: when we rename binders, we also need to rename all names bound to them 
;; in the terms that export them!

;; Emits syntax for a function that freshens values in accordance with the binding spec
;; The function takes a value and a boolean indicating whether we're "at" the top level
(define (freshener bs top-level?-name)

  ;; An assoc mapping nonterminal references (that have been imported)
  ;; to their freshened version and to the names of the renamings that
  ;; need to be applied.
  ;; Complicating matters, we can't name the renaming as a whole
  ;; (we don't know what Redex language we're in), so we need to
  ;; call the renaming by a pattern like `((variable_from-98 variable_to-98) ...)' 
  (define renaming-info (make-renaming-info (bspec-ported-nts bs)))

  (define extra-...ed-names
    (append*
     (map (match-lambda 
           [`(,_ ,bfreshened-nt ,σ-name ,depth) 
            (syntax-case σ-name ()
              [((from-name to-name) dotdotdot)
               `((,bfreshened-nt ,depth) (,#`from-name ,(+ depth 1)) (,#`to-name ,(+ depth 1)))])])
          renaming-info)))
  
  (define transcriber
    (transcribe-match bs extra-...ed-names
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
                   (first (freshen/rec (term #,nt))))])]))
  
  #`(redex-let* #,(bspec-lang-name bs)
    ;; define the renamings we'll use:
      (#,@(bfreshener renaming-info (bspec-exported-nts bs) top-level?-name))
                
      `(, #,transcriber ;; new version of `v`
        , #,(beta->subst-merger (bspec-export-beta bs) renaming-info)))) ;; exports

;; top-level?-name is expected to be #`#t or #`#f
(define (vanilla-freshener-clauses top-level?-syn)
  (if (syntax-e top-level?-syn)
      `(, #`[any (term (any ()))])
      `(, #`[(any (... ...)) (term ((any (... ...)) ()))]
          , #`[variable-not-otherwise-mentioned 
               ;; This is the gensym that's at the heart of everything
               (let ((freshened-v (gensym (term variable-not-otherwise-mentioned))))
                 `(,freshened-v ((,(term variable-not-otherwise-mentioned) ,freshened-v))))]
        , #`[any (term (any ()))])))


(module+ phase-1-test

         
 (define uq 'unquote) ;; oh boy
 ;; PS: wait a sec... match doesn't interpolate...
 
 (check-match
  (syntax->datum (freshener lambda-bspec #`top-level?))
  `(redex-let* ,_ ([(,x-bfreshened ,x-σ)
                    (if (xor #f top-level?)
                        (freshen/rec (term x))
                        (noop-binder-substitution-plus-orig (term x)))])
     `((,uq (term (,bf-name
                   (,x-bfreshened)
                   (,uq (rename-references
                         (interp-beta (term ,x-σ))
                         (term
                          (,uq (if (symbol? (term expr))
                                   (term expr)
                                   (first (freshen/rec (term expr)))))))))))
       (,uq (interp-beta (term ()))))))

 (check-match
  (syntax->datum (freshener ieie-bspec #`top-level?))
  `(redex-let* ,_ ([(,ie-ren ,ie-σ) ,_]
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
       (,uq (interp-beta (term (,shad ,e-σ ,ie-σ)))))))
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

  #`(redex-let* #,(bspec-lang-name bs)
                (#,@σ-clauses)
                #,(beta->subst-merger (bspec-export-beta bs) renaming-info)))

(define (vanilla-noop-substituter)
  `(, #`[(any (... ...)) `()]
    , #`[variable `((,(term variable) ,(term variable)))]
    , #`[any '()]))

(module+ phase-1-test
 (check-match
  (syntax->datum (noop-substituter lambda-bspec))
  `(redex-let* ,_
               ()
               (interp-beta (term ())))) ;; lambda doesn't export anything
 

 
 (check-match
  (syntax->datum (noop-substituter ieie-bspec))
  `(redex-let* ,_
               ([,e-σ (term (,uq (noop-binder-substitution (term ,e))))]
                [,ie-σ (term (,uq (noop-binder-substitution (term ,ie))))])
               (interp-beta (term (,shadow ,e-σ ,ie-σ))))))


(module+ phase-1-test
 (define let*-clause-bspec
   (surface-bspec->bspec #'((x expr_val let*-clause_next #:refers-to x)
                            #:exports (shadow x let*-clause_next))
                         #'scheme #'let*))

 ;; TODO: check binder-freshening behavior
 )



;; Use `somethinger` to generate handlers for all the binding forms in `bses`.
(define (invocation-match somethinger vanilla-somethinger
                          bses lang-name . extra-args)
  #`(term-match/single #,lang-name
      #,@(map (lambda (bs)
                #`[#,(bspec-redex-pattern bs)
                   #,(apply somethinger `(,bs . ,extra-args))])
              bses)
      #,@(apply vanilla-somethinger extra-args)))


;; Each of `freshener`, `noop-substituter`, `reference-renamer`, and `binder-renamer`
;; expects to be transcribed in a place where `(bspec-redex-pattern bs)` has been
;; matched against the value in question

(define (setup-functions bses lang-name body)
  #`(parameterize
     ([cur-language-fns
       (language-functions
        ;; language-functions-freshen/rec (this one is never at the top level)
        #,(invocation-match freshener vanilla-freshener-clauses
                            bses lang-name #`#f)
        ;; language-functions-noop-binder-subst
        #,(invocation-match noop-substituter vanilla-noop-substituter
                            bses lang-name)
        ;; language-functions-ref-rename
        (lambda (σ v)
          (#,(invocation-match reference-renamer vanilla-reference-renamer
                               bses lang-name #`σ) v))
        ;; language-functions-bnd-rename
        (lambda (σ v)
          (#,(invocation-match binder-renamer vanilla-binder-renamer
                               bses lang-name #`σ) v)))])
     #,body))




(define (possibly-freshener bses lang-name)
  #`(lambda (v)
      #,(setup-functions ;; TODO: do we want to lift out a definition of the `language-functions`?
         bses lang-name
         ;; we only want the freshened value, not the subst
         #`(first (#,(invocation-match freshener vanilla-freshener-clauses
                                       bses lang-name #`#t) v)))))


;; == Tying everything together ==




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

 (require rackunit) 
 (require "reduction-semantics.rkt")
 
 ;; === fine-grained tests ===

 
 
 

 (define-syntax (setup-binding-forms stx)
   (syntax-case stx ()
     [(setup-binding-forms lang-name (binder-info ...) body ...)
      (setup-functions
       (parse-binding-forms #`(binder-info ...) #`lang-name)
       #`lang-name
       #`(begin body ...))]))

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
    (siamese-lambda ((x ...) expr #:refers-to (rib x ...)) ...))

   ;; ==== reference-rename ====
   (check-equal?
    (rename-references `((a aa)) `(lambda (a) (a b)))
    `(lambda (a) (aa b)))
   
   (check-equal?
    (rename-references `((a aa) (b bb) (c cc) (d dd) (e ee) (f ff))
                       `(ieie a b c
                              (a (b (c (d (e (f g))))))
                              (a (b (c (d (e (f g))))))))
    `(ieie a b c
           (aa (bb (cc (dd (ee (ff g))))))
           (aa (bb (cc (dd (ee (ff g))))))))

   
   ;; ==== binder-rename ====
   (check-equal?
    (rename-binders `((x xx) (b bb) (c cc)) `(lambda (x) (a b)))
    `(lambda (xx) (a b)))

   (check-equal?
    (rename-binders `((a aa) (b bb) (c cc) (d dd) (e ee) (f ff))
                    `(ieie a b c
                           (a (b (c (d (e (f g))))))
                           (a (b (c (d (e (f g))))))))
    `(ieie aa bb cc
           (a (b (c (d (e (f g))))))
           (a (b (c (d (e (f g))))))))

   (check-equal?
    (rename-binders `((a aa) (c cc))
                    `(cl a 4 (cl b (a 5) (cl c (b (a 6)) no-cl))))
    `(cl aa 4 (cl b (a 5) (cl cc (b (a 6)) no-cl))))



   ;; (need more tests here!)

   ;; ==== freshen/rec ====

   (check-match
    (freshen/rec
     `(ieie a b c (a (b (c d))) (a (b (c d)))))
    `((ieie a ,bb ,cc (a (b (,cc d))) (a (b (,cc d)))) ((b ,bb) (c ,cc)))
    (and (not (eq? bb `b)) (not (eq? cc `c))))
   

   ) ;; end setup-binding-forms
 )




(module+ test
 ;; === coarse-grained tests ===


 (define-syntax (define-freshener stx)
   (syntax-case stx ()
     [(define-freshener freshener-name lang-name binder-info ...)
      #`(define freshener-name
          #,(possibly-freshener
             (parse-binding-forms #`(binder-info ...) #`lang-name)
             #`lang-name))]))

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
    (siamese-lambda ((x ...) expr #:refers-to (rib x ...)) ...))


 (check-match (big-freshener `(lambda (x) x))
              `(lambda (,x) ,x) ;; structure was preserved
              (not (eq? x `x))) ;; we actually freshened the name
 
 (check-equal? (big-freshener 1) 1)


 (define (totally-destructure d v)
   (match (d v)
          [(list sub-v ...) (map (lambda (sv) (totally-destructure d sv)) sub-v)]
          [atom atom]))


 (check-match
  (totally-destructure 
   big-freshener
   `(let* (cl a 4 (cl b (a 5) (cl c (b (a 6)) no-cl))) (a (b c))))
  `(let* (cl ,aa 4 (cl ,bb (,aa 5) (cl ,cc (,bb (,aa 6)) no-cl))) (,aa (,bb ,cc)))
  (and (not (equal? 'a aa)) (not (equal? 'b bb)) (not (equal? 'c cc))))

 ;; check that shadowing works properly
 (check-match
  (totally-destructure 
   big-freshener
   `(let* (cl  a 1 (cl  a  a no-cl))  a))
  ` (let* (cl ,a 1 (cl ,b ,a no-cl)) ,b)
  (not (equal? a b)))


 (check-match
  (totally-destructure
   big-freshener
   `(let3* ((a 1) (b a) (c (a b)))
           (a (b c))))
  `(let3* ((,aa 1) (,bb ,aa) (,cc (,aa ,bb)))
          (,aa (,bb ,cc)))
  (and (not (equal? 'a aa)) (not (equal? 'b bb)) (not (equal? 'c cc))))


 (check-match
  (totally-destructure big-freshener `(va-lambda (a b c) (a (b (c d)))))
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







;; TODO: worry about things like `(rib a_!_1)`







