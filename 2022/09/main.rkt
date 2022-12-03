#lang typed/racket

(require bnf
         unreachable
         "../../utils.rkt")

(Pos . ≜ . (Pairof Integer Integer))
(Dir . ≜ . (U "L" "R" "U" "D"))
(Rope . ≜ . (Listof Pos))

(: move : Rope Dir → Rope)
(define (move rope dir)
  (match-define (cons head tails) rope)
  (define head* (move-head head dir))
  (cons head*
        (let keep-up : Rope ([head : Pos head*] [tails : Rope tails])
          (match tails
            ['() '()]
            [(cons tail tails*)
             (define tail* (keep-up-tail head tail))
             (cons tail* (keep-up tail* tails*))]))))

(: keep-up-tail : Pos Pos → Pos)
(define (keep-up-tail head tail)
  (match-define (cons x₁ y₁) head)
  (match-define (cons x₂ y₂) tail)
  (cond [(in-touch? x₁ y₁ x₂ y₂) tail]
        [(= x₁ x₂) (cond [(> y₂ y₁) (cons x₂ (sub1 y₂))]
                         [(< y₂ y₁) (cons x₂ (add1 y₂))])]
        [(= y₁ y₂) (cond [(> x₂ x₁) (cons (sub1 x₂) y₂)]
                         [(< x₂ x₁) (cons (add1 x₂) y₂)])]
        [else (cons (if (> x₂ x₁) (sub1 x₂) (add1 x₂))
                    (if (> y₂ y₁) (sub1 y₂) (add1 y₂)))]))

(: move-head : Pos Dir → Pos)
(define (move-head pos dir)
  (match-define (cons x y) pos)
  (match dir
    ["L" (cons (- x 1) y)]
    ["R" (cons (+ x 1) y)]
    ["U" (cons x (+ y 1))]
    ["D" (cons x (- y 1))]))

(: in-touch? : Integer Integer Integer Integer → Boolean)
(define (in-touch? x₁ y₁ x₂ y₂)
  (and (<= (abs (- x₁ x₂)) 1)
       (<= (abs (- y₁ y₂)) 1)))

(define (steps [n : Integer])
  (define pos₀ (cons 0 0))
  (for*/fold ([r : Rope (make-list n pos₀)]
              [acc : (Setof Pos) (set)])
             ([l (in-input)]
              [event (in-value (string-split l))]
              [dir (in-value (cast (first event) Dir))]
              [_ (in-range (assert (string->number (second event)) exact-integer?))])
    (define r* (move r dir))
    (values r* (set-add acc (last r*)))))

(define (q1)
  (define-values (st touched) (steps 2))
  (set-count touched))

(define (q2)
  (define-values (st touched) (steps 10))
  (set-count touched))

(module+ main
  (displayln (q1))
  (displayln (q2)))
