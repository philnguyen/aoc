#lang typed/racket

(require bnf
         unreachable
         "../../utils.rkt")

(require/typed "input.rkt" #;"demo.rkt"
                 [input (Listof Cube)])

(: count-by-dim : Integer Integer Integer (Listof Cube) → Integer)
(define (count-by-dim i j k cubes)
  (define indices
    (for/fold ([counts : (HashTable Pos (Listof Integer)) (hash)])
              ([c (in-list cubes)])
      ((inst hash-update Pos (Listof Integer)) counts (cons (list-ref c i) (list-ref c j)) (λ (s) (cons (list-ref c k) s)) (λ ()'()))))
  (for/sum : Integer ([(p ks) (in-hash indices)])
    (* 2 (count-consecutives (sort ks <=)))))

(: free-surfaces : (Listof Cube) → Integer)
(define (free-surfaces cubes)
  (define cube-set (list->set cubes))

  ;; Compute the boundaries
  (define-values (min-x max-x min-y max-y min-z max-z)
    (for/fold ([min-x : Integer 999999]
               [max-x : Integer -1]
               [min-y : Integer 999999]
               [max-y : Integer -1]
               [min-z : Integer 999999]
               [max-z : Integer -1])
              ([c (in-list cubes)])
      (match-define (list x y z) c)
      (values (min min-x x) (max max-x x) (min min-y y) (max max-y y) (min min-z z) (max max-z z))))
  (define (in-x-range) (in-range (- min-x 1) (+ max-x 2)))
  (define (in-y-range) (in-range (- min-y 1) (+ max-y 2)))
  (define (in-z-range) (in-range (- min-z 1) (+ max-z 2)))

  ;; Compute connected cube chunks
  (define-values (union! find) ((inst make-union-find Cube)))

  (for* ([x (in-x-range)]
         [y (in-y-range)])
    (for* ([z (in-z-range)]
           [c₁ (in-value (list x y z))]
           [c₂ (in-value (list x y (+ 1 z)))]
           #:unless (or (set-member? cube-set c₁)
                        (set-member? cube-set c₂)))
      (union! c₁ c₂)))
  (for* ([x (in-x-range)]
         [z (in-z-range)])
    (for* ([y (in-y-range)]
           [c₁ (in-value (list x y z))]
           [c₂ (in-value (list x (+ 1 y) z))]
           #:unless (or (set-member? cube-set c₁)
                        (set-member? cube-set c₂)))
      (union! c₁ c₂)))
  (for* ([y (in-y-range)]
         [z (in-z-range)])
    (for* ([x (in-x-range)]
           [c₁ (in-value (list x y z))]
           [c₂ (in-value (list (+ 1 x) y z))]
           #:unless (or (set-member? cube-set c₁)
                        (set-member? cube-set c₂)))
      (union! c₁ c₂)))

  ;; Get chunk connected to boundaries
  (define air-cube : Cube (find (list (- min-x 1) (- min-y 1) (- max-y 1))))

  ;; For each cube, check the surfaces that are in the air chunk
  (for/sum : Integer ([c (in-list cubes)])
    (match-define (list x y z) c)
    (for/sum : Integer ([c (in-list (list (list x y (+ z 1))
                                          (list x y (- z 1))
                                          (list x (+ y 1) z)
                                          (list x (- y 1) z)
                                          (list (+ x 1) y z)
                                          (list (- x 1) y z)))]
                        #:when (equal? (find c) air-cube))
      1)))

(define count-consecutives : ((Listof Integer) → Integer)
  (match-lambda
    [(list* x y xs) #:when (= y (+ 1 x)) (+ 1 (count-consecutives (cons y xs)))]
    [(list* _ xs) (count-consecutives xs)]
    [_ 0]))

(define (q1)
  (- (* 6 (length input))
     (+ (count-by-dim 0 2 1 input)
        (count-by-dim 0 1 2 input)
        (count-by-dim 1 2 0 input))))

(define (q2)
  (free-surfaces input))

(module+ main
  (displayln (q1))
  (displayln (q2)))
