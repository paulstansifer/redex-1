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
 

 (define-language let*-language
   (e (e e)
      (my-let* clauses e)
      x
      number)
   (x variable-not-otherwise-mentioned)
   (clauses (clause x e clauses)
            ()))

 (test-binding-forms
  ((clause x e clauses #:refers-to x) #:exports (shadow clauses x)
   (my-let* clauses e #:refers-to clauses))
  let*-language)

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

 ;; check that shadowing works properly
 (check-match
  (totally-destructure
   (my-let* `(my-let* ,(clause `(clause a 1 ,(clause `(clause a a ()))))
                      a)))
  `(my-let* (clause ,a 1 (clause ,b ,a ()))
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

 )
