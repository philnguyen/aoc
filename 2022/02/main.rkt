#lang typed/racket
(require bnf
         "../../utils.rkt")

(Shape . ::= . 'rock 'paper 'scissors)
(Outcome . ::= . 'lose 'draw 'win)

(define decode : (String → Shape)
  (match-lambda
    [(or "A" "X") 'rock]
    [(or "B" "Y") 'paper]
    [(or "C" "Z") 'scissors]))

(define beats? : (Shape Shape → Boolean)
  (match-lambda**
    [('rock 'scissors) #t]
    [('scissors 'paper) #t]
    [('paper 'rock) #t]
    [(_ _) #f]))

(define shape-score : (Shape → Integer)
  (match-lambda
    ['rock 1]
    ['paper 2]
    ['scissors 3]))

(: score : Shape Shape → Integer)
(define (score s₁ s₂)
  (define match-score
    (cond [(beats? s₁ s₂) 0]
          [(beats? s₂ s₁) 6]
          [else 3]))
  (+ match-score (shape-score s₂)))

(define decode-strategy : (String → Outcome)
  (match-lambda
    ["X" 'lose]
    ["Y" 'draw]
    ["Z" 'win]))

(define appropriate-shape : (Shape Outcome → Shape)
  (match-lambda**
   [(s 'draw) s]
   [('rock 'win) 'paper]
   [('rock 'lose) 'scissors]
   [('paper 'win) 'scissors]
   [('paper 'lose) 'rock]
   [('scissors 'win) 'rock]
   [('scissors 'lose) 'paper]))

(module+ main
  (displayln
   (for/sum : Integer ([l (in-input)])
     (match-define (list s₁ s₂) (string-split l))
     (score (decode s₁) (decode s₂))))
  (displayln
   (for/sum : Integer ([l (in-input)])
     (match-define (list s₁ s₂) (string-split l))
     (define shape₁ (decode s₁))
     (define shape₂ (appropriate-shape shape₁ (decode-strategy s₂)))
     (score shape₁ shape₂))))

