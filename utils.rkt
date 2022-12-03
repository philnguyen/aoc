#lang typed/racket

(provide (all-defined-out))

(require unreachable
         bnf
         (only-in typed/racket/base
                  [in-lines b:in-lines]))

(define (in-input) (in-list (file->lines "input.txt")))

(define (in-input-line-groups) : (Sequenceof (Listof String))
  (define-values (rev-res rev-acc-last)
    (for/fold ([acc : (Listof (Listof String)) '()]
               [acc-cur : (Listof String) '()])
              ([l (in-input)])
      (match l
        ["" (values (cons (reverse acc-cur) acc) '())]
        [_ (values acc (cons l acc-cur))])))
  (in-list
   (reverse (match rev-acc-last
              ['() rev-res]
              [_ (cons (reverse rev-acc-last) rev-res)]))))

(define (in-input-n-lines [n : Integer]) : (Sequenceof (Listof String))
  (define-values (rev-res rev-acc-last)
    (for/fold ([acc : (Listof (Listof String)) '()]
               [acc-cur : (Listof String) '()])
              ([l (in-input)]
               [i (in-naturals)])
      (define acc-cur* (cons l acc-cur))
      (cond [(= (remainder i n) (- n 1)) (values (cons (reverse acc-cur*) acc) '())]
            [else (values acc acc-cur*)])))
  (in-list
   (reverse (match rev-acc-last
              ['() rev-res]
              [_ (cons (reverse rev-acc-last) rev-res)]))))

(define (in-input-chars) : (Sequenceof Char) (in-input-port-chars (open-input-file "input.txt")))

(define-syntax-rule (for/count clauses body ...)
  (for/sum : Integer clauses (if (let () body ...) 1 0)))

(: int : String → Integer)
(define (int s) (assert (string->number s) exact-integer?))

(: float : String → Float)
(define (float s) (assert (string->number s) flonum?))

(: step-input (∀ (S X) S (String → X) (S X → S) → S))
(define (step-input s₀ interp-line step)
  (for/fold ([s : S s₀]) ([l (in-input)])
    (step s (interp-line l))))

(define tails : (∀ (X) (Listof X) → (Listof (Listof X)))
  (match-lambda
    ['() (list '())]
    [(and xs (cons _ xs*)) (cons xs (tails xs*))]))

(define within : ((Option Integer) (Option Integer) → Integer → Boolean)
  (λ (lo hi)
    (λ (n)
      (and (implies lo (<= lo n))
           (implies hi (<= n hi))))))

(: iter : (∀ (X) Integer (X → X) X → X))
(define (iter n f x)
  (for/fold ([x : X x]) ([_ (in-range n)])
    (f x)))

((Grid X) . ≜ . (Vectorof (Vectorof X)))
(Pos . ≜ . (Pairof Integer Integer))
(Cube . ≜ . (List Integer Integer Integer))

(: grid-ref (∀ (X) (→ X) → (Grid X) Pos → X))
(define ((grid-ref mk-default) grid pos)
  (match-define (cons row col) pos)
  (cond [(and (<= 0 row (sub1 (vector-length grid)))
              (<= 0 col (sub1 (vector-length (vector-ref grid row)))))
         (vector-ref (vector-ref grid row) col)]
        [else (mk-default)]))

(define Pos+ : (Pos Pos → Pos)
  (match-lambda**
   [((cons row₁ col₁) (cons row₂ col₂)) (cons (+ row₁ row₂) (+ col₁ col₂))]))

(define Cube+ : (Cube Cube → Cube)
  (match-lambda**
   [((list x₁ y₁ z₁) (list x₂ y₂ z₂)) (list (+ x₁ x₂) (+ y₁ y₂) (+ z₁ z₂))]))

(: count-up (∀ (X) ([(HashTable X Integer) X] [Integer] . ->* . (HashTable X Integer))))
(define (count-up counts k [d 1])
  ((inst hash-update X Integer) counts k (λ (n) (+ n d)) (λ () 0)))

(require typed/racket/unsafe)
(unsafe-require/typed
 profile
 [profile-thunk (∀ (X) (→ X) #:delay Real #:order Any → X)])
(provide profile-thunk)

(: make-union-find (∀ (X) (→ (Values (X X → Void) (X → X)))))
;; Given set of all elements, return functions for:
;; - Marking two elements as belonging to the same partition
;; - Finding a representative element, given one
(define (make-union-find)
  (define parent : (Mutable-HashTable X X) (make-hash))
  (define rank : (Mutable-HashTable X Integer) (make-hash))
  (define (parent-of [x : X]) (hash-ref parent x (λ () x)))
  (define (rank-of [x : X]) (hash-ref rank x (λ () 0)))

  (: union! : X X → Void)
  ;; Mark `x` and `y` as belonging in the same partition
  (define (union! x y)
    (define x* (find x))
    (define y* (find y))
    (unless (equal? x* y*)
      (define-values (x:root x:root:rank y:root y:root:rank)
        (let ([x*:rank (rank-of x*)]
              [y*:rank (rank-of y*)])
          (if (< x*:rank y*:rank)
              (values y* y*:rank x* x*:rank)
              (values x* x*:rank y* y*:rank))))
      (hash-set! parent y:root x:root)
      (when (= x:root:rank y:root:rank)
        (hash-set! rank x:root (add1 x:root:rank)))))

  (: find : X → X)
  ;; Return the element that represents `x`
  (define (find x)
    (match (parent-of x)
      [(== x) x]
      [(app find x*) (hash-set! parent x x*)
                     x*]))

  (values union! find))
