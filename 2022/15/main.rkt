#lang typed/racket

(require bnf
         unreachable
         "../../utils.rkt")

(define test-input : (Listof (Pairof Pos Pos))
  '(((2 . 18) . (-2 . 15))
    ((9 . 16 ) . (10 . 16))
    ((13 . 2 ) . (15 . 3))
    ((12 . 14 ) . (10 . 16))
    ((10 . 20 ) . (10 . 16))
    ((14 . 17 ) . (10 . 16))
    ((8 . 7 ) . (2 . 10))
    ((2 . 0 ) . (2 . 10))
    ((0 . 11 ) . (2 . 10))
    ((20 . 14 ) .  (25 . 17))
    ((17 . 20 ) . (21 . 22))
    ((16 . 7 ) . (15 . 3))
    ((14 . 3 ) . (15 . 3))
    ((20 . 1 ) . (15 . 3))))

(define input : (Listof (Pairof Pos Pos))
  '(((155404 . 2736782) . (2062250 . 2735130))
    ((2209843 . 541855) . (2159715 . 2000000))
    ((3437506 . 3046523) .  (3174767 . 2783059))
    ((925392 . 1508378) .  (941123 . 1223290))
    ((2349988 . 3272812) .  (1912017 . 3034331))
    ((292610 . 374034) .  (941123 . 1223290))
    ((2801735 . 1324309) .  (2159715 . 2000000))
    ((3469799 . 2027984) .  (3174767 . 2783059))
    ((3292782 . 2910639) .  (3174767 . 2783059))
    ((3925315 . 2646100) .  (3174767 . 2783059))
    ((1883646 . 2054943) .  (2159715 . 2000000))
    ((2920303 . 3059306) .  (3073257 . 3410773))
    ((2401153 . 2470599) .  (2062250 . 2735130))
    ((2840982 . 3631975) .  (3073257 . 3410773))
    ((1147584 . 3725625) .  (1912017 . 3034331))
    ((2094987 . 2782172) .  (2062250 . 2735130))
    ((3973421 . 982794) .  (3751293 . -171037))
    ((2855728 . 2514334) .  (3174767 . 2783059))
    ((1950500 . 2862580) .  (1912017 . 3034331))
    ((3233071 . 2843812) .  (3174767 . 2783059))
    ((2572577 . 3883463) .  (3073257 . 3410773))
    ((3791570 . 3910685) .  (3073257 . 3410773))
    ((3509554 . 311635) .  (3751293 . -171037))
    ((1692070 . 2260914) .  (2159715 . 2000000))
    ((1265756 . 1739058) .  (941123 . 1223290))))

(define the-input : (Parameterof (Listof (Pairof Pos Pos))) (make-parameter test-input))

(: cannot-be-beacon? : Pos → Boolean)
(define (cannot-be-beacon? pos)
  (and (not
        (for/or : Boolean ([sensor-beacon (in-list (the-input))])
          (match-define (cons sensor beacon) sensor-beacon)
          (or (equal? pos sensor)
              (equal? pos beacon))))
       (for/or : Boolean ([sensor-beacon (in-list (the-input))])
         (match-define (cons sensor beacon) sensor-beacon)
         (<= (manhattan-distance sensor pos)
             (manhattan-distance sensor beacon)))))

(define manhattan-distance : (Pos Pos → Integer)
  (match-lambda**
   [((cons x₁ y₁) (cons x₂ y₂)) (+ (abs (- x₁ x₂)) (abs (- y₁ y₂)))]))

(define (q1)
  (parameterize ([the-input input])
    (define max-dist (apply max
                            (for/list : (Listof Integer) ([p (in-list (the-input))])
                              (match-define (cons sensor beacon) p)
                              (manhattan-distance sensor beacon))))
    (define min-x (apply min (for/list : (Listof Integer) ([sensor-beacon (in-list (the-input))])
                               (match-define (cons (cons x₁ _) (cons x₂ _)) sensor-beacon)
                               (min x₁ x₂))))
    (define max-x (apply max (for/list : (Listof Integer) ([sensor-beacon (in-list (the-input))])
                               (match-define (cons (cons x₁ _) (cons x₂ _)) sensor-beacon)
                               (max x₁ x₂))))
    (for/sum : Integer ([x (in-range (- min-x max-dist) (+ 1 max-dist max-x))]
                        #:when (cannot-be-beacon? (cons x 2000000)))
      1))
  )

(define (q2)
  (parameterize ([the-input input])
    (define N 4000000)

    (: perim : Pos Integer → (Setof Pos))
    (define (perim pos d)
      (match-define (cons x y) pos)
      (for/fold ([acc : (Setof Pos) (set)])
                ([y* (in-range (- y d) (+ y d 1))])
        (define dy (abs (- y y*)))
        (define dx (- d dy))
        (set-add (set-add acc (cons (+ x dx) y*)) (cons (- x dx) y*))))

    (define sensor-and-range
      (for/list : (Listof (Pairof Pos Integer)) ([p (in-list (the-input))])
        (match-define (cons sensor beacon) p)
        (cons sensor (manhattan-distance sensor beacon))))

    (define (outside-all-range? [p : Pos])
      (for/and : Boolean ([l (in-list sensor-and-range)])
        (match-define (cons sensor d) l)
        (> (manhattan-distance sensor p) d)))

    (define (within [n : Integer] [pos : Pos])
      (match-define (cons x y) pos)
      (and (<= 0 x n) (<= 0 y n)))

    (define candidates : ((Pairof Pos Pos) → (Setof Pos))
      (match-lambda
        [(cons sensor beacon)
         (define d (manhattan-distance sensor beacon))
         (for/set : (Setof Pos) ([p (in-set (perim sensor (+ 1 d)))]
                                 #:when (within N p)
                                 #:when (outside-all-range? p))
           p)]))
    
    (define all-candidates
      (match-let ([(cons p ps) (the-input)])
        (for/fold ([s : (Setof Pos) (candidates p)])
                  ([p (in-list ps)]
                   #:break (not (set-empty? s)))
          (set-union s (candidates p)))))
    (match-define (list (cons x y)) (set->list all-candidates))
    (+ (* x 4000000) y)))

(module+ main
  (displayln (q1))
  (displayln (q2)))
