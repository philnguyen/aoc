#lang typed/racket

(require bnf
         unreachable
         "../../utils.rkt"
         "input.rkt")

(Board . ::= . (Board [rows : Integer]
                      [cols : Integer]
                      [content : (Setof Pos)]
                      [tries : (Listof (Pairof (Listof Shift) Shift))]))
(Shift . ≜ . (Pos → Pos))

(define input : (Parameterof String) (make-parameter test-input))

(define-syntax-rule (define-move name (row col) (row* col*))
  (define name : Shift
    (match-lambda [(cons row col) (cons row* col*)])))
(define-move N (row col) ((sub1 row) col))
(define-move S (row col) ((add1 row) col))
(define-move E (row col) (row (add1 col)))
(define-move W (row col) (row (sub1 col)))
(define NE (compose N E))
(define NW (compose N W))
(define SW (compose S W))
(define SE (compose S E))

(: next-pos : Board Pos → Pos)
(define (next-pos board pos)
  (match-define (Board rows cols content tries) board)

  (: free? : Shift → Boolean)
  (define (free? shift) (not (set-member? content (shift pos))))

  (or
   (and (andmap free? (list N E S W NE NW SE SW)) pos)
   (for/or : (Option Pos) ([try (in-list tries)])
     (match-define (cons checks shift) try)
     (and (andmap free? checks) (shift pos)))
   pos))

(: re-order : (∀ (X) (Listof X) → (Listof X)))
(define (re-order xs)
  (match-define (cons x xs*) xs)
  (append xs* (list x)))

(define adjacents : (Pos → (Listof Pos))
  (match-lambda
    [(cons row col) (list (cons (add1 row) col)
                          (cons (sub1 row) col)
                          (cons row (add1 col))
                          (cons row (sub1 col))
                          (cons (add1 row) (add1 col))
                          (cons (add1 row) (sub1 col))
                          (cons (sub1 row) (add1 col))
                          (cons (sub1 row) (sub1 col)))]))

(: step : Board → Board)
(define (step board)
  (match-define (Board rows cols elves tries) board)
  (define considers : (HashTable Pos (Listof Pos)) ; target -> sources
    (for/fold ([acc : (HashTable Pos (Listof Pos)) (hash)])
              ([elf (in-set elves)])
      (define pos (next-pos board elf))
      ((inst hash-update Pos (Listof Pos))
       acc pos (λ ([srcs : (Listof Pos)]) (cons elf srcs)) (λ () '()))))
  (define elves*
    (for/fold ([acc : (Setof Pos) (set)])
              ([(tgt srcs) (in-hash considers)])
      (match srcs
        [(list _) (set-add acc tgt)]
        [_ (set-union acc (list->set srcs))])))
  (Board rows cols elves* (re-order tries)))

(: run : Board Integer → Board)
(define (run board n)
  (for/fold ([b : Board board]) ([_ (in-range n)])
    (step b)))

(define (read-board)
  (define ls (string-split (input) "\n"))
  (define content
    (for*/fold ([content : (Setof Pos) (set)])
               ([(l row) (in-indexed ls)]
                [(c col) (in-indexed l)])
      (match c
        [#\# (set-add content (cons row col))]
        [#\. content])))
  (Board (length ls)
         (string-length (first ls))
         content
         (list (cons (list N NE NW) N)
               (cons (list S SE SW) S)
               (cons (list W NW SW) W)
               (cons (list E NE SE) E))))

(define (q1)
  (match-define (and board (Board rows cols content _)) (run (read-board) 10))
  (define-values (min-row max-row min-col max-col)
    (for/fold ([min-row : Integer rows]
               [max-row : Integer -1]
               [min-col : Integer cols]
               [max-col : Integer -1])
              ([pos (in-set content)])
      (match-define (cons row col) pos)
      (values (min min-row row)
              (max max-row row)
              (min min-col col)
              (max max-col col))))
  (- (* (add1 (- max-row min-row))
        (add1 (- max-col min-col)))
     (for/sum : Integer ([pos (in-set content)])
       (match-define (cons row col) pos)
       (if (and (<= min-row row max-row)
                (<= min-col col max-col))
           1
           0))))

(: draw-board : Board → Void)
(define (draw-board board)
  (match-define (Board rows cols content _) board)
  (for ([r (in-range rows)])
    (printf "~n")
    (for ([c (in-range cols)])
      (printf "~a" (cond [(set-member? content (cons r c)) "#"]
                         [else "."]))))
  (printf "~n"))

(define (q2)
  (let loop : Integer ([i : Integer 1]
                       [b : Board (read-board)])
    (define b* (step b))
    (cond [(equal? (Board-content b*) (Board-content b)) i]
          [else (loop (+ 1 i) b*)])))

(module+ main
  (parameterize ([input real-input])
    (displayln (q1))
    (displayln (q2))))
