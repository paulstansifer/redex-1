#lang racket
(require redex)

;; A binding-object is an opaque piece of syntax with binding information.
;; * destructure is a zero-argument function that emits a list of subterms.
;;   Thanks to `gensym`, it needs no other information to generate fresh terms
;;   each time. For example, the binding-object corresponding to `#'(lambda (x) x)`
;;   might (when invoked, to destructure it) return `(list #'(x57) #'x57)`
;; The remaining fields are for internal use only. 

(struct binding-object (destructure ref-rename bnd-rename bnd-freshen))

;; === Renaming ===

(define (rename-references σ v)
  (match v
         [(list sub-v ...) (map (lambda (x) (rename-references σ x)) sub-v)]
         [(binding-object _ rr _ _) (rr σ)]
         [(? symbol? s)
          (match (assoc s σ)
                 [`(,_ ,new-s) new-s]
                 [#f s])]))

(define (rename-binders σ v)
  (match v
         [(list sub-v ...) (map (lambda (x) (rename-binders σ x)) sub-v)]
         [(binding-object _ _ br _) (br σ)]
         [(? symbol? s)
          (match (assoc s σ)
                 [`(,_ ,new-s) new-s]
                 [#f s])]))

(module+ test
 (require rackunit)
 
 (define σ '((a aa) (s ss) (h hh)))
 
 (check-equal? (rename-references σ
                                  '(t h i (s i s (a (t) e) s) t))
               '(t hh i (ss i ss (aa (t) e) ss) t))
 
 )

;; === Freshening ===

;; Generate a map from free (exported) binders in the argument
;; to fresh names.
;; (corresponds to v ⋈ v in the Romeo paper)
(define (freshen-binders v)
  (match v
         [(list sub-v ...) '()] ;; sequences export nothing
         [(binding-object _ _ _ bf) (bf)]
         ;; This gensym is what ultimately does all name freshening:
         [(? symbol? s) `((,s ,(gensym)))]))


