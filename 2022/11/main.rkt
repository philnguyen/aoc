#lang typed/racket

(require bnf
         unreachable
         "../../utils.rkt")

(Monkey-Id . ≜ . Integer)
(Monkey . ≜ . (Integer → (Pairof Monkey-Id Integer)))
(State . ≜ . (HashTable Monkey-Id (Listof Integer)))
(Count . ≜ . (HashTable Monkey-Id Integer))
(Count×State . ≜ . (Pairof Count State))

(define process-worry-level : (Parameterof (Integer → Integer)) (make-parameter (λ ([n : Integer]) (quotient n 3))))

(: monkey : (Integer → Integer) Integer Monkey-Id Monkey-Id → Monkey)
(define ((monkey f n m₁ m₂) old)
  (define new ((process-worry-level) (f old)))
  (cons (if (= 0 (remainder new n)) m₁ m₂)
        new))

(define monkeys : (HashTable Monkey-Id Monkey)
  (hash 0 (monkey (λ (n) (* n 5)) 11 2 3)
        1 (monkey (λ (n) (* n 11)) 5 4 0)
        2 (monkey (λ (n) (+ n 2)) 19 5 6)
        3 (monkey (λ (n) (+ n 5)) 13 2 6)
        4 (monkey (λ (n) (* n n)) 7 0 3)
        5 (monkey (λ (n) (+ n 4)) 17 7 1)
        6 (monkey (λ (n) (+ n 6)) 2 7 5)
        7 (monkey (λ (n) (+ n 7)) 3 4 1)))

(define test-monkeys : (HashTable Monkey-Id Monkey)
  (hash 0 (monkey (λ (n) (* n 19)) 23 2 3)
        1 (monkey (λ (n) (+ n 6)) 19 2 0)
        2 (monkey (λ (n) (* n n)) 13 1 3)
        3 (monkey (λ (n) (+ n 3)) 17 0 1)))

(define state₀ : State
  (hash 0 '(83 88 96 79 86 88 70)
        1 '(59 63 98 85 68 72)
        2 '(90 79 97 52 90 94 71 70)
        3 '(97 55 62)
        4 '(74 54 94 76)
        5 '(58)
        6 '(66 63)
        7 '(56 56 90 96 68)))

(define test-state₀ : State
  (hash 0 '(79 98)
        1 '(54 65 75 74)
        2 '(79 60 97)
        3 '(74)))

(: run : (HashTable Monkey-Id Monkey) → Count×State → Count×State)
(define ((run monkeys) count×state)
  (for*/fold ([count×state : Count×State count×state])
             ([mid (in-range (hash-count (cdr count×state)))]
              [m (in-value (hash-ref monkeys mid))]
              [item (in-list (hash-ref (cdr count×state) mid))])
    (match-define (cons mid* item*) (m item))
    (cons (count-up (car count×state) mid)
          (hash-set
           ((inst hash-update Monkey-Id (Listof Integer))
            (cdr count×state) mid* (λ (items) (append items (list item*))) list)
           mid '()))))

(define (run* [iters : Integer])
  (match-define (cons c s) (iter iters (run monkeys) (cons ((inst hash Monkey-Id Integer)) state₀)))
  (apply * (take (sort (hash-values c) >=) 2)))

(define (q1) (run* 20))

(define (q2)
  (define N (* 2 3 5 7 11 13 17 19 23))
  (parameterize ([process-worry-level (λ (n) (remainder n N))])
    (run* 10000)))

(module+ main
  (displayln (q1))
  (displayln (q2)))
