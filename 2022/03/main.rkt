#lang typed/racket
(require bnf
         "../../utils.rkt")

(Rucksack . ≜ . String)
(Item . ≜ . Char)

(define priority : (Item → Integer)
  (match-lambda
    [(? char-lower-case? item) (+ 1 (- (char->integer item) (char->integer #\a)))]
    [(? char-upper-case? item) (+ 27 (- (char->integer item) (char->integer #\A)))]))

(define elems : (Rucksack → (Setof Item)) (λ (s) (list->set (string->list s))))

(: first-common : (∀ (X) (Setof X) (Setof X) * → X))
(define (first-common xs . xss)
  (set-first (apply set-intersect xs xss)))

(: common-in-halves : Rucksack → Char)
(define (common-in-halves rs)
  (define l (string-length rs))
  (define m (assert (/ l 2) exact-nonnegative-integer?))
  (first-common (elems (substring rs 0 m))
                (elems (substring rs m l))))

(define (q1)
  (for/sum : Integer ([l (in-input)])
    (priority (common-in-halves l))))

(define (q2)
  (for/sum : Integer ([l (in-input-n-lines 3)])
    (match-define (list its₁ its₂ its₃) (map elems l))
    (priority (first-common its₁ its₂ its₃))))

(module+ main
  (displayln (q1))
  (displayln (q2)))
