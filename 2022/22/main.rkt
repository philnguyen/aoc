#lang typed/racket

(require bnf
         unreachable
         "../../utils.rkt"
         "input.rkt")

(Cell . ::= . #\. #\# #\space)
(Instr . ::= . Integer 'R 'L)
(Dir . ::= . '↑ '→ '↓ '←)
(Board . ::= . (Board [content : (HashTable Pos Cell)]
                      [rows : Integer]
                      [cols : Integer]))
(State . ::= . (State [pos : Pos] [dir : Dir]))

(define maze-input : (Parameterof String) (make-parameter test-maze-input))
(define instructions : (Parameterof String) (make-parameter test-instructions))

(define cw : (Dir → Dir)
  (match-lambda
    ['↑ '→]
    ['→ '↓]
    ['↓ '←]
    ['← '↑]))

(define ccw : (Dir → Dir)
  (match-lambda
    ['↑ '←]
    ['← '↓]
    ['↓ '→]
    ['→ '↑]))

(define real-input-wrap : (Board State → State)
  (match-lambda**
   [((Board content rows cols) (State pos dir))
    (match-define (cons row col) pos)
    (cond
      ;; 1
      [(and (= row -1) (<= 50 col 99))
       (State (cons (+ 150 col) 0) '→)]
      [(and (<= 0 row 49) (= col 49))
       (State (cons (- 150 row) 0) '→)]
      ;; 2
      [(and (= row -1) (<= 100 col 149))
       ???]
      [(and (<= 0 row 49) (= col 150))
       ???]
      [(and (= row 50) (<= 100 col 149))
       ???]
      ;; 3
      [(and (<= 50 row 99) (= col 49))
       ???]
      [(and (<= 50 row 99) (= col 100))
       ???]
      ;; 4
      [(and (= row 99) (<= 0 col 49))
       ???]
      [(and (<= 100 row 149) (= col -1))
       ???]
      ;; 5
      [(and (<= 100 row 149) (= col 100))
       ???]
      [(and (= row 150) (<= 50 col 99))
       ???]
      ;; 6
      [(and (<= 150 row 199) (= col -1))
       ???]
      [(and (<= 150 row 199) (= col 50))
       ???]
      [(and (= row 200) (<= 0 col 49))
       ???])]))

(: board-ref : Board Pos → Char)
(define (board-ref board pos) (hash-ref (Board-content board) pos (λ () #\space)))

(: follow : Board Integer State → Pos)
(define (follow board δ state)
  (match-define (State pos dir) state)
  (match-define (Board _ rows cols) board)
  (define shift : (Pos → Pos)
    (match-lambda
      [(cons row col)
       (match dir
         ['↑ (cons (modulo (sub1 row) rows) col)]
         ['↓ (cons (modulo (add1 row) rows) col)]
         ['→ (cons row (modulo (add1 col) cols))]
         ['← (cons row (modulo (sub1 col) cols))])]))
  (for/fold ([pos : Pos pos])
            ([i (in-range δ)])
    (let loop ([pos* : Pos (shift pos)])
      (match (board-ref board pos*)
        [#\space (loop (shift pos*))]
        [#\# pos]
        [#\. pos*]))))

(: move : Board Instr State → State)
(define (move board instr state)
  #;(printf "~a -- ~a -->~n" state instr)
  (match-define (State pos dir) state)
  (define state*
    (match instr
      ['R  (State pos (cw dir))]
      ['L (State pos (ccw dir))]
      [(? integer? n) (State (follow board n state) dir)]))
  #;(printf "      ~a~n" state*)
  state*)

(: draw-board : Board → Void)
(define (draw-board b)
  (match-define (Board content rows cols) b)
  (for ([r (in-range rows)])
    (printf "~n")
    (for ([c (in-range cols)])
      (printf "~a" (board-ref b (cons r c)))))
  (printf "~n"))

(define (read-board)
  (let* ([ls (string-split (maze-input) "\n")]
         [content
          (for*/fold ([content : (HashTable Pos Cell) (hash)])
                     ([(l row) (in-indexed ls)]
                      [(cᵢ col) (in-indexed l)]
                      #:unless (equal? cᵢ #\space))
            (hash-set content (cons row col) (cast cᵢ Cell)))])
    (Board content (length ls) (string-length (argmax string-length ls)))))

(define (read-instrs)
  (let-values ([(n rev-instrs)
                (for/fold ([current : Integer 0]
                           [rev-instrs : (Listof Instr) '()])
                          ([c (in-string (instructions))])
                  (match c
                    [#\R (values 0 (list* 'R current rev-instrs))]
                    [#\L (values 0 (list* 'L current rev-instrs))]
                    [_ (define d (- (char->integer c) (char->integer #\0)))
                       (values (+ (* 10 current) d) rev-instrs)]))])
    (reverse (cons n rev-instrs))))

(define (solve)
  (define board (read-board))
  #;(draw-board board)

  (for/fold ([st : State (State (cons 0 0) '→)])
            ([i (in-list (read-instrs))])
    (move board i st)))

(define (q1)
  (parameterize ([maze-input real-maze-input]
                 [instructions real-instructions])
    (match-define (State (cons row col) dir) (solve))
    (+ (* 1000 (add1 row))
       (* 4 (add1 col))
       (match dir
         ['→ 0]
         ['↓ 1]
         ['← 2]
         ['↑ 3]))))

(module+ main
  (displayln (q1)))
