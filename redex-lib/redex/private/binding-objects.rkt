#lang racket
;; A binding-object is an opaque piece of syntax with binding information.
;; * destructure is a zero-argument function that emits a list of subterms.
;;   Thanks to `gensym`, it needs no other information to generate fresh terms
;;   each time. For example, the binding-object corresponding to `#'(lambda (x) x)`
;;   might (when invoked, to destructure it) return `(list #'(x57) #'x57)`
;; * exported-binders is a list of symbols indicating what binders the
;;   object exports, for use by other syntax objects

(struct binding-object (destructure exported-binders))

;; Generate a map from free (exported) binders in the argument
;; to fresh names.
;; (corresponds to bo ⋈ bo in the Romeo paper)
#;(define (freshen-binders bo)
  )
