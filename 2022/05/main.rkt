#lang typed/racket
(require bnf
         "../../utils.rkt")

(Stack . ≜ . (Listof Symbol))
(Stacks . ≜ . (HashTable Integer Stack))

(define stacks : Stacks
  (hasheq 1 '(R C H)
          2 '(F S L H J B)
          3 '(Q T J H D M R)
          4 '(J B Z H R G S)
          5 '(B C D T Z F P R)
          6 '(G C H T)
          7 '(L W P B Z V N S)
          8 '(C G Q J R)
          9 '(S F P H R T D L)))

(: tops : Stacks → (Listof Symbol))
(define (tops stacks)
  (for/list ([i (in-range 1 (+ 1 (hash-count stacks)))])
    (first (hash-ref stacks i))))

(: move : Stacks Integer Integer → Stacks)
(define (move stacks from to)
  (match-define (cons x xs) (hash-ref stacks from))
  (match-define ys (hash-ref stacks to))
  (hash-set (hash-set stacks from xs) to (cons x ys)))

(: move-n : Stacks Integer Integer Integer → Stacks)
(define (move-n stacks count from to)
  (for/fold ([acc : Stacks stacks]) ([_ (in-range 0 count)])
    (move acc from to)))

(: move-batch-n : Stacks Integer Integer Integer → Stacks)
(define (move-batch-n stacks count from to)
  (define xs (hash-ref stacks from))
  (define ys (hash-ref stacks to))
  (define-values (xs₁ xs₂) (split-at xs count))
  (hash-set (hash-set stacks from xs₂) to (append xs₁ ys)))

(: run-with : (Stacks Integer Integer Integer → Stacks) → Stack)
(define (run-with step)
  (tops
   (for/fold ([stacks : Stacks stacks]) ([l (in-input)])
     (match-define (list s₁ s₂ s₃) (map int (string-split l ",")))
     (step stacks s₁ s₂ s₃))))

(define (q1) (run-with move-n))
(define (q2) (run-with move-batch-n))

(module+ main
  (displayln (q1))
  (displayln (q2)))
