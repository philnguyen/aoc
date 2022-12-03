#lang typed/racket

(require bnf
         unreachable
         "../../utils.rkt")

(define ref (grid-ref (λ () 1000)))

(define (char->elevation [c : Char]) : Integer
  (case c
    [(#\S) (char->elevation #\a)]
    [(#\E) (char->elevation #\z)]
    [else (- (char->integer c) (char->integer #\a))]))

(define start? ((inst make-parameter (Char → Any)) (λ (c) (equal? c #\S))))

(define (load-grid) : (Values (Listof Pos) Pos (Grid Integer))
  (define starts : (Listof Pos) '())
  (define ends : (Listof Pos) '())
  (define grid
    (for/vector : (Grid Integer) ([l (in-input)] [row (in-naturals)])
      (for/vector : (Vectorof Integer) ([c (in-string l)] [col (in-naturals)])
        (when ((start?) c)
          (set! starts (cons (cons row col) starts)))
        (when (equal? c #\E)
          (set! ends (cons (cons row col) ends)))
        (char->elevation c))))
  (values starts (first ends #|assume only 1|#) grid))

(: explore : (Grid Integer) (Listof Pos) Pos → Integer)
(define (explore grid starts end)
  (let loop : Integer ([seen : (Setof Pos) (set)]
                       [path : Integer 0]
                       [frontier : (Setof Pos) (list->set starts)])
    (cond
      [(set-empty? frontier) (error "end at ~a" path)]
      [(set-member? frontier end) path]
      [else
       (define candidates
         (for*/set : (Setof Pos) ([f (in-set frontier)]
                                  [row (in-value (car f))]
                                  [col (in-value (cdr f))]
                                  [p (in-list (list (cons row (add1 col))
                                                    (cons row (sub1 col))
                                                    (cons (add1 row) col)
                                                    (cons (sub1 row) col)))]
                                  #:unless (set-member? seen p)
                                  #:when (<= (ref grid p) (add1 (ref grid f))))
           p))
       (loop (set-union seen frontier)
             (+ 1 path)
             candidates)])))

(define (q1)
  (define-values (starts end grid) (load-grid))
  (explore grid starts end))

(define (q2)
  (parameterize ([start? (λ (c) (member c '(#\S #\a)))])
    (q1)))

(module+ main
  (displayln (q1))
  (displayln (q2)))
