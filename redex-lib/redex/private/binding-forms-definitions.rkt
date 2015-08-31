#lang racket

(provide (all-defined-out))

;; When this error occurs, it seems to come from 'wrap-modbeg.rkt'. That seems bad
(define-syntax (shadow stx) (raise-syntax-error 'shadow "used outside of binding specification"))
(define-syntax (rib stx) (raise-syntax-error 'rib "used outside of binding specification"))
(define-syntax (nothing stx) (raise-syntax-error 'nothing "used outside of binding specification"))

(struct import/internal (body beta) #:prefab)
(struct .../internal (body drivers) #:prefab) 

(struct shadow/internal (betas) #:prefab)
(struct rib/internal (betas) #:prefab)

;; body: a tree, with `import/internal`s, `.../internal`s, and identifiers,
;;       representing the binding strucutre
;; export-beta: a beta indicating what `nt`s get exported
;; imported-nts: a list of nonterminals that are imported somewhere within this value
;; exported-nts: a list of nonterminals that appear in `export-beta`
;; ported-nts: a (duplicate-free) list of nonterminals on the previous two lists
;; transcription-depths: a list of pairs of names appearing in `body` and numbers indicating 
;;       how many `...`s they are under
(struct bspec
        (body export-beta imported-nts exported-nts ported-nts transcription-depths)
        #:prefab)


