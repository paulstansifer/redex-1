#lang racket
(provide binding-object destructure noop-binder-substitution rename-references rename-binders destructure/rec)

;; A binding-object is an opaque piece of syntax with binding information.
;; Its fields are for internal use only; use `destructure` to extract its
;; structure.
;; * ((binding-object-destructure/rec) top-level?) ... well, it's complex,
;;   but it's the heart of `-destructure`.
;; * ((binding-object-noop-binder-sibst)) emits a no-op σ whose range is
;;   the exported binders of the syntax.
;; * ((binding-object-ref-rename bo) σ) emits a new binding object with its
;;   references renamed according to σ
;; * ((binding-object-bnd-rename bo) σ) emits a new binding object with its
;;   binders renamed according to σ
;; * ((binding-object-freshen-binders bo)) emits a σ mapping its exported
;;   binders to fresh names

(struct binding-object
        (destructure destructure/rec noop-binder-subst ref-rename bnd-rename))

;; === Renaming ===

(define (rename-references σ v)
  (match v
         [(list sub-v ...) (map (lambda (x) (rename-references σ x)) sub-v)]
         [(binding-object _ _ _ rr _) (rr σ)]
         [(? symbol? s)
          (match (assoc s σ)
                 [`(,_ ,new-s) new-s]
                 [#f s])]
         [anything-else anything-else]))

(define (rename-binders σ v)
  (match v
         [(list sub-v ...) (map (lambda (x) (rename-binders σ x)) sub-v)]
         [(binding-object _ _ _ _ br) (br σ)]
         [(? symbol? s)
          (match (assoc s σ)
                 [`(,_ ,new-s) new-s]
                 [#f s])]
         [anything-else anything-else]))
 
(module+ test
 (require rackunit)
 
 (define σ '((a aa) (s ss) (h hh)))
 
 (check-equal? (rename-references σ
                                  '(t h i (s i s (a (t) e) s) t))
               '(t hh i (ss i ss (aa (t) e) ss) t)))

;; === Freshening ===
;; Destructure a form, freshening exposable atoms in the process
(define (destructure v)
  (match v
    [(binding-object des _ _ _ _) (des)]
    ;; No binding structure at this level:     
    [anything-else anything-else]))



;; Returns a new `v` with its exported binders (and the things that import them)
;; freshened, and the substitution that freshened them. (it is assumed that
;; whatever `v` exports is exported to the top level (otherwise,
;; `noop-binder-subst` is what you want))
(define (destructure/rec v)
  (match v
    [(list sub-v ...) `(,v ())] ;; nothing exported
    [(binding-object _ dr _ _ _) (dr)]
    ;; Exported, so it's a binder.
    [(? symbol? s)
     ;; This gensym is what ultimately does all name freshening:
     (let ((new-s (gensym))) `(,new-s ((,s ,new-s))))]
    [anything-else `(,v ())]))

;; Generate a substitution that doesn't change anything, but whose
;; range is all the binders in `v`
(define (noop-binder-substitution v)
  (match v
         [(list sub-v ...) '()] ;; sequences export nothing
         [(binding-object _ _ nbs _ _) (nbs)]
         [(? symbol? s) `((,s ,s))]
         [anything-else '()]))



