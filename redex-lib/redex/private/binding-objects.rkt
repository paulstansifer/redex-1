#lang racket
(provide binding-object binding-object-destructure rename-references rename-binders freshen-binders)

;; A binding-object is an opaque piece of syntax with binding information.
;; * ((binding-object-destructure bo)) emits a list of subterms.
;;   Thanks to `gensym`, it needs no other information to generate fresh terms
;;   each time. For example, the binding-object corresponding to `(term (lambda (x) x))`
;;   might (when invoked, to destructure it) return `(list (term (x57)) (term x57))`
;;
;; The remaining fields are for internal use only. 
;; * ((binding-object-ref-rename bo) σ) emits a new binding object with its
;;   references renamed according to σ
;; * ((binding-object-bnd-rename bo) σ) emits a new binding object with its
;;   binders renamed according to σ
;; * ((binding-object-freshen-binders bo)) emits a σ mapping its exported
;;   binders to fresh names

(struct binding-object (destructure bnd-freshen ref-rename bnd-rename))

;; === Renaming ===

(define (rename-references σ v)
  (match v
         [(list sub-v ...) (map (lambda (x) (rename-references σ x)) sub-v)]
         [(binding-object _ _ rr _) (rr σ)]
         [(? symbol? s)
          (match (assoc s σ)
                 [`(,_ ,new-s) new-s]
                 [#f s])]))

(define (rename-binders σ v)
  (match v
         [(list sub-v ...) (map (lambda (x) (rename-binders σ x)) sub-v)]
         [(binding-object _ _ _ br) (br σ)]
         [(? symbol? s)
          (match (assoc s σ)
                 [`(,_ ,new-s) new-s]
                 [#f s])]))

(module+ test
 (require rackunit)
 
 (define σ '((a aa) (s ss) (h hh)))
 
 (check-equal? (rename-references σ
                                  '(t h i (s i s (a (t) e) s) t))
               '(t hh i (ss i ss (aa (t) e) ss) t)))

;; === Freshening ===

;; Generate a map from free (exported) binders in the argument
;; to fresh names.
;; (corresponds to v ⋈ v in the Romeo paper)
(define (freshen-binders v)
  (match v
         [(list sub-v ...) '()] ;; sequences export nothing
         [(binding-object _ bf _ _) (bf)]
         ;; This gensym is what ultimately does all name freshening:
         [(? symbol? s) `((,s ,(gensym)))]))






