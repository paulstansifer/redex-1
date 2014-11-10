#lang racket
(require "binding-objects.rkt")
(require rackunit)

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
(define-syntax (import/internal stx) (raise-syntax-error 'import/internal "used outside of binding specification"))



(define (names-mentioned-in-beta beta)
  (remove-duplicates (names-mentioned-in-beta/rec beta)))

(define (names-mentioned-in-beta/rec beta)
  (syntax-case beta (nothing)
    [nothing '()]
    [(op . betas)
     (append* (map names-mentioned-in-beta/rec (syntax->list #'betas)))]
    [name (list (syntax->datum #'name))]))

(module+
 test
 (check-equal? (names-mentioned-in-beta #'a) '(a))
 (check-equal? (names-mentioned-in-beta #'(shadow (rib a b c) (shadow b c d e)
                                                  (rib f nothing g h a a a) b
                                                  nothing nothing))
               '(a b c d e f g h)))



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

       ;; everything below here gets moved into `pattern-and-transcriber`

       ;; the `redex-pattern` has all the binding-specfic stuff stripped,
       ;; and is ready for `redex-match`ing.
       (define-values (top-level-binding-pattern top-level-redex-pattern)
         (let process-bf-body [(bf-body #'bf-body)
                               (binding-pattern '()) (redex-pattern '())]
           (syntax-case bf-body ()
             [() binding-pattern]
             [(bpat #:refers-to imports-beta . rest-of-body)
              (process-bf-body #'rest-of-body
                               (append binding-pattern #'(import/internal bpat beta)))]
             [(bpat #:refers-to)
              (raise-syntax-error 'define-language
                                  "#:refers-to requires an argument"
                                  #f bf-body)]
             [(#:refers-to . rest-of-body)
              (raise-syntax-error 'define-language
                                  "#:refers-to requires an expression to its left"
                                  #f bf-body)]
             [(bpat . rest-of-body)
              (process-bf-body #'rest-of-body (append binding-pattern #'bpat))])))

       (cons (cons #'bf-name (list exports top-level-binding-pattern))
             (parse-binding-forms rest-of-bfs)))]
    [() '()]))

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


