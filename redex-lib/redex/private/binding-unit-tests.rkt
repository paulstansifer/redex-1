#lang racket

(require "binding-forms.rkt")
(require "binding-objects.rkt")
(require "reduction-semantics.rkt")
(require rackunit)
(require (only-in "term.rkt" term))



;; These tests properly belong in binding-forms.rkt, but they need
;; to take place in a different phase.
(module+ test
 (define-syntax test-binding-forms setup-binding-forms)

 (define-language my-lambda-calc
   (e (e e)
      (my-lambda (x) e)
      x)
   (x variable-not-otherwise-mentioned))

 
 (test-binding-forms
  ((my-lambda (x) e #:refers-to x))
  my-lambda-calc)

 (define id (my-lambda '(my-lambda (x) x)))
 

 (check-match (destructure id)
              `(my-lambda (,x) ,x))
 

 (define-language more-complex-language
   (e (e e)
      (my-let* any e)
      x
      number)
   (x variable-not-otherwise-mentioned)
   (clauses (clause x e clauses)
            ()))

 (test-binding-forms
  ((clause x e clauses #:refers-to x) #:exports (shadow clauses x)
   (my-let* clauses e #:refers-to clauses))
  more-complex-language)

 (define basic-clauses
   (clause `(clause a 4
                    ,(clause `(clause b (a 5)
                                      ,(clause `(clause c (b (a 6)) ())))))))
 
 (define basic-let* (my-let* `(my-let* ,basic-clauses (a (b c)))))


 (define (totally-destructure v)
   (match v
     [(binding-object destr _ _ _ _)
      (totally-destructure (destr))]
     [(list sub-v ...) (map totally-destructure sub-v)]
     [atom atom]))


 (check-match 
  (totally-destructure basic-let*)
  `(my-let* (clause ,a 4 (clause ,b (,a 5) (clause ,c (,b (,a 6)) ())))
            (,a (,b ,c)))) 
 )
