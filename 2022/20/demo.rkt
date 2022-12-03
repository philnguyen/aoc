#lang typed/racket
(provide (all-defined-out))

(define test-input : (Immutable-Vectorof Integer)
  (vector-immutable 1
                    2
                    -3
                    3
                    -2
                    0
                    4))
