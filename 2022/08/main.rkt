#lang typed/racket
(require bnf
         unreachable
         "../../utils.rkt")

(define ref ((inst grid-ref Integer) (λ () -1)))

(: visible? : (Grid Integer) Pos → Boolean)
(define (visible? grid pos)
  (match-define (cons row col) pos)
  (define h (ref grid pos))
  (or (for/and : Boolean ([row* (in-range 0 row)])
         (> h (ref grid (cons row* col))))
       (for/and : Boolean ([row* (in-range (add1 row) (vector-length grid))])
         (> h (ref grid (cons row* col))))
       (for/and : Boolean ([col* (in-range 0 col)])
         (> h (ref grid (cons row col*))))
       (for/and : Boolean ([col* (in-range (add1 col) (vector-length (vector-ref grid row)))])
         (> h (ref grid (cons row col*))))))

(: count-visibles : (Grid Integer) → Integer)
(define (count-visibles grid)
  (for*/sum : Integer ([row (in-range (vector-length grid))]
                       [col (in-range (vector-length (vector-ref grid row)))]
                       #:when (visible? grid (cons row col)))
    1))

(: scenic-scope : (Grid Integer) Pos → Integer)
(define (scenic-scope grid pos)
  (match-define (cons row col) pos)
  (define h (ref grid pos))
  (* (for/sum : Integer ([row* (in-range (sub1 row) -1 -1)]
                         #:final (>= (ref grid (cons row* col)) h))
       1)
     (for/sum : Integer ([row* (in-range (add1 row) (vector-length grid))]
                         #:final (>= (ref grid (cons row* col)) h))
       1)
     (for/sum : Integer ([col* (in-range (sub1 col) -1 -1)]
                         #:final (>= (ref grid (cons row col*)) h))
       1)
     (for/sum : Integer ([col* (in-range (add1 col) (vector-length (vector-ref grid row)))]
                         #:final (>= (ref grid (cons row col*)) h))
       1)))

(: best-scenic-scope : (Grid Integer) → Integer)
(define (best-scenic-scope grid)
  (define best : Integer 1)
  (for* ([row (in-range 0 (vector-length grid))]
         [col (in-range 0 (vector-length (vector-ref grid row)))])
    (set! best (max best (scenic-scope grid (cons row col)))))
  best)

(define (the-grid)
  (for/vector : (Grid Integer) ([l (in-input)])
    (for/vector : (Vectorof Integer) ([c (in-list (string->list l))])
      (- (char->integer c) (char->integer #\0)))))

(define (q1) (count-visibles (the-grid)))
(define (q2) (best-scenic-scope (the-grid)))

(module+ main
  (displayln (q1))
  (displayln (q2)))
