#lang racket

(provide (all-defined-out))

(struct tm (content) #:transparent)

(define count-to-1000 0)

(define (1000th-report str)
  (set! count-to-1000 (add1 count-to-1000))
  (when (= 0 (modulo count-to-1000 250))
        (printf (string-append str " " (number->string count-to-1000) "\n"))))

(define (from-term t) 
  (1000th-report "from-term")
  (a-non-t (tm-content (a-t t))))
(define (to-term t) 
  (1000th-report "to-term")
  (tm (a-non-t t)))

(define (maybe-to-term t)
  (1000th-report "maybe-to-term")
  (if (tm? t)
      t
      (tm t)))

(define (a-t t [generous #t])
  ;;(1000th-report "a-t")
  (unless (tm? t) 
          (unless generous (printf "Expected ~s to be a term, but it wasn't.~n" t))
          (unless generous (tm-content t))) ;; make a backtracing error
  (if (tm? t) t (tm t)))

(define (has-term? t)
  ;;(1000th-report "has-term?")
  (match (if (syntax? t) (syntax->datum t) t)
    [(tm _) #t]
    [`(,a . ,d) (or (has-term? a) (has-term? d))]
    [_ #f]))

(define (a-non-t t [generous #f])
  ;;(1000th-report "a-not-t")
  (when (has-term? t)
        (unless generous (printf "Didn't expect ~s to be (or contain) a term, but it was.~n" t))
        (unless generous (tm-content 879878))) ;; make a backtracing error
  t)

(define (from-term/traced t) 
  (1000th-report "from/traced")
  (printf "f[~s]~n" (tm-content t))
  (a-non-t (tm-content (a-t t))))
(define (to-term/traced t) 
  (1000th-report "to/traced")
  (printf "t[~s]~n" t)
  (tm (a-non-t t)))

(define (term->list t)
  (define t-for-real (a-t t))
  (1000th-report "term->list")
  (define result
    (if (list? (tm-content t-for-real))
        (map tm (tm-content t-for-real))
        #f))
  ;;(printf "⋆~s⋆~n" t)
  result)

;; expects an IMPROPER LIST, whose end is a term.
;; because that's the way that the list case in `term.rkt` works
(define (list->term l)
  (to-term 
   (let loop ([l l])
     (if (pair? l)
         (cons (from-term (car l))
               (loop (cdr l)))
         (from-term l)))))

(define (list->term* . l)
  (to-term (ttrace (map from-term (ttrace l)))))

#;(define (ttrace thing)
  (printf "~s~n" thing)
  thing)

(define-syntax-rule (ttrace thing)
  (call-with-values (lambda () thing)
    (lambda vals
      (define prettier-vals (map (lambda (v) (if (syntax? v) (syntax->datum v) v)) vals))

      (printf "~s~n" prettier-vals)
      (apply values vals))))

(define (term-null? t)
  (null? (tm-content t)))

(define (term-car t)
  (tm (car (tm-content t))))

(define (term-cdr t)
  (tm (car (tm-content t))))

(define (term-cons a d)
  (tm (cons (tm-content a) (tm-content d))))
