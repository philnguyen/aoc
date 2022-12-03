#lang typed/racket

(require "../../utils.rkt")

(: first-diffs : (∀ (X) (Listof X) Integer → Integer))
(define (first-diffs xs n)
  (let loop ([xs : (Listof X) xs] [i : Integer 0])
    (define xs₀ (take xs n))
    (if (= n (set-count (list->set xs₀)))
        (+ n i)
        (loop (rest xs) (+ 1 i)))))

(define (q1) (first-diffs (sequence->list (in-input-chars)) 4))
(define (q2) (first-diffs (sequence->list (in-input-chars)) 14))

(module+ main
  (displayln (q1))
  (displayln (q2)))
