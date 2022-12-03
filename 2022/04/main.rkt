#lang typed/racket
(require bnf
         "../../utils.rkt")

(Section . ≜ . (Pairof Integer Integer))
(Section-Pair . ≜ . (Pairof Section Section))

(define contains? : (Section Section → Boolean)
  (match-lambda**
   [((cons lo₁ hi₁) (cons lo₂ hi₂)) (<= lo₁ lo₂ hi₂ hi₁)]))

(define overlaps? : (Section Section → Boolean)
  (match-lambda**
   [((cons lo₁ hi₁) (cons lo₂ hi₂))
    (not (or (< hi₁ lo₂) (< hi₂ lo₁)))]))

(define (section-pairs) : (Listof Section-Pair)
  (for/list ([l (in-input)])
    (match-define (list s₁ s₂) (string-split l ","))
    (define (sec [s : String]) : Section
      (match-define (list lo hi) (string-split s "-"))
      (cons (int lo) (int hi)))
    (cons (sec s₁) (sec s₂))))

(: count-pairs-by : (Section Section → Boolean) → Integer)
(define (count-pairs-by p?)
  ((inst count Section-Pair)
   (match-lambda [(cons s₁ s₂) (p? s₁ s₂)])
   (section-pairs)))

(define (q1)
  (count-pairs-by (λ (s₁ s₂) (or (contains? s₁ s₂) (contains? s₂ s₁)))))

(define (q2)
  (count-pairs-by (λ (s₁ s₂) (overlaps? s₁ s₂))))

(module+ main
  (displayln (q1))
  (displayln (q2)))
