#lang typed/racket

(require bnf
         unreachable
         "../../utils.rkt")

(define test-input-1
  "#.#####
#.....#
#>....#
#.....#
#...v.#
#.....#
#####.#")

(define test-input-2
  "#.######
#>>.<^<#
#.<..<<#
#>v.><>#
#<^v^^>#
######.#")

(define real-input
  "#.########################################################################################################################
#<<<^<^^>v<<^<^><><v<^<<.v^><<<v>><^v<vv>v<vv>^>>^^^^.>>^vv<^<<>^.vv.<>>v>v^>^<><.vv^v.^<^v>^vv<^vv<<>v<<>><<<v^^>v><<<^>#
#>^^v><.<>>v.v.^>v^..>^<vv>v^><v^<<>v>>.^v^vv^^>.^><^>>^>vv>>v^>vvvv^v^vv<<^<^>^>^v<v^>><><v^^^<v.^v<>^.>v><vv.^<^^^^<>>>#
#<<.><>v<>.v^<^^v<^^>.^.>>v.^^^v>^^^.<><.^.<>>^<>.v><^^^>^>^^^^><vv^.v^<<^v>v^^^<<<^<..^vv><.^v<vv^>>vv>v.><v^>>^<v^>>vv>#
#.><^v.>^v>>vv><^>.>>>>>^.>>.>^v>v^>v^^>v^^..>^.^<^.v<>v<<<^^^.vvv>>.<>^vvv>>.^<^v^>^<^<vv>^>^.<>^<<>v.<<<.^<>^>.<v.vvv^>#
#>><v<>.v><<^^vvv<<<^>^v^v><^>^<>>v.<.<>^<>vv>vv>^.v><<<^<v^vvv.<<<><^<^<^.^^vv>^v^^v<>>vv^<^.^v^v<v^>^.>.v>v^^<v<^<>^>v>#
#>>><v<.>>v^<.^vvvv<v<^<<v>>v>vv.^><v^.>>vv><<.<^.^v>^^><>^<^v<vvvvv<<<<^^>..>>>v^^>.vv<>.^^^.<v>v^>>^>^^>v^v^^<.>>^^<.<>#
#<<v>>v<>^><^v<>^>vvv..v.^.<^.v.vv^.<.v<>v>^<^v^<^>><.<>v^v>^<<^<v^^<v^<v^.<v><<<>^^<><>.v><^^^<<^<v>><vv<^<^.^<<^.^<<v>>#
#>>>^^>v^>^>>v><<>^<v><>>^>.<v<<>v<>^<>^v.<<^.^^^^>^.v>v><v^>vv^^^.>v^<v^^v<<^.vv^>vvv>^>>v<.^^vv<<v.v..^v.^vvv.<.>^<^v>>#
#><^vv^>>v.<^<v^^><v^>^><<<v^>v><v^^>><vv^><.>>^vv>><vv<^v^v^>^>>.vvvvvv<>>>.>^<vv^<vv<<<^^v^>.v><^.<<^<>^^>.^v><^^vv.^>>#
#>..<<v<<>>.<^v<<.>v^<..^<^^v^>.><.<v>>v><<>^>>v<vvv>>v<v>.vvvv<.<<<^<^v>^<v^>>v.^v^<^v..^..<^<><>^<<>^>^<<^^.>^^<v<>v<><#
#<v^v>v<^^<v>>vv^v<..^>v>>>.>^^<>>>^..>>>^<<^<^<>^<v>>^>>><^v^v^<.^<<<^v^.^^^<v>>><^^<>>><..vv.^.^<<v^v.>>^v^^><>><.v^>v>#
#.<^^<v>v.<v<^.^v^<.v^vvv^vv^<..v<.>>>v<<>>vv>>^.>^.v>vv>.v^<<v^>>v.<^^<^<<>^^.^^>^>>^<^<<^^vv^^.<.><^.>^^<>v<.^v<>v><v<.#
#>^.v^^><^<.>^v>v><>>>..>.v>vvv<<vv^.>v>.>v.<^vv.^>^vvv>.>v^v>>.>^^<<>>.^.>>>^>v<>v>v^^<>^<^.^><.vv^^<<.^v>>.>>>.^>^^^^^<#
#..^>vv><^^.>>^^.<<<v..<<>^.<.<^^.v<<<^<<>><>v>v<^^^.<><^<<>v^^<^v^>^v>v<<^<<v<><<>.><..<^vv^<.><>^^><<.>>^.^v><>v^<^v>^>#
#><<>v>.>^<<v>>>>>^>v..<vv<^<v>>^<<^v<v<<<<.v^>v.v<^>>>v.^><^><>.<>.^v><><<v>^^^^.<<.>^>><>.<<.<^<.^>..^>^.^>^v^v.<.^v>><#
#><><^v.<<<<>>v<<<<^v<<^^<><<.>^^.^.^.<>vv<<<v>^<><^^<^>^>^^.v<^>>vv^v.>^.<<><vv>>.>.<><^<.<<>.v>.^>>>^<<>.<v>^^v^v^<>.<<#
#<^>^v^>v^v.<^^>.^>^<<>.<.<<vvv>v>v^v^vvv>v^v^v<^^^<^>>v.^v.^>v><.^^^<>^>^^vv.v>>>^v<<>>^<^.v^>>>><v>v><^<.^v^v^^.<<>><^<#
#>^>v.><v<^<><>><v<^^<^><<<<^v>^<v^>v<<>^>>.><v<v<^^>^<><><^<.<.<><v^^.^>>v^v^.>><vvvv^v^vv><<^<<^>.v>>>vv>v^v^^<v^^>^>><#
#<<v^^>vv^^v.<<v<v<^><^v.>.<^v^>^^>^<^^v>>v<^^vv<>^v^.^v<>.<^^>^^v><>^^v.><.v^^>.<<.v^<v<^<>^<^><v^>.>^v>v<v<.>v<.<v.>.<<#
#>^<<v^vv..vv^v><>>>^>v.>v^..^>^vv>^^>v^v<>.><v<<<<^><>v^.v^>.>^vv>vv>.>^<<.v<^^v^<<>^^^>^.<.v>^><.<^<^>>><.<<^^^>^<^<v<>#
#<^><v<v><<<>v>>vv.>^<v>><>v>^.v^<v><<^<>>^<^^.<v<<vv>^v.v.<vv<^<<^>v>v.<<<v^><^^>.>>v>.<^vv.^v>^^^<><<^<>>><v^v>>>v<^>v>#
#>>>^.v><<<>^v<.<.^><v>><>.<.<>v^v>>>^<^^vvv.vv<v<^^^>><^v>>>v>v<>v<v<vv^.^>v<>^>>>^<<v<vv^>><.v<^v<v^<.<>v>^>^><.>v<>.><#
#<^<v>v.vv>vv^v<.>>.v.^..>^v<.v><>^<.^^<v><^.v^<v^vv^^v^<>>^<^><v.vvv^>.^v>><<>><<<>.<v^<^.<vv^.v<><v^v^>^v^>v<<v^>vv>^v>#
#<><.v.^v>>><^.<.^<<v>^^><<^>>.^^.v>vv^^.v>^<<^^<<<^>>^>^>v..^v><>v<vv<<v^v<>>><v>^v<><.>v>v>v^^.^>>vv^v.vv<>v^<><^^><vv<#
#<<v<v>^><^v^<^<v>><.v<.>^vv^>^<v^v>v<.vvv<v<^^>^^^^v^<<v^>v<v^vv>.^vv>v^.>>.^<.>>v<..^v.>^<<v<vvv^<..^<<>^^>v<<><^^><>>>#
########################################################################################################################.#")

(define input : (Parameterof String) (make-parameter test-input-1))

(Dir . ::= . #\^ #\v #\> #\<)
(Winds . ≜ . (HashTable Pos (Listof Dir)))
(Ctx . ::= . (Ctx [rows : Integer]
                  [cols : Integer]
                  [walls : (Setof Pos)]
                  [target : Pos]
                  [winds : Winds]))
(State . ≜ . (Setof Pos))

(: add-wind : Winds Pos Dir → Winds)
(define (add-wind m p d)
  (hash-update m p (λ ([ds : (Listof Dir)]) (sort (cons d ds) char<=?)) (λ () '())))

(define (read-board) : (Values Ctx State)
  (define ls (string-split (input) "\n"))
  (define rows (length ls))
  (define cols (string-length (first ls)))
  (define-values (walls winds)
    (for*/fold ([walls : (Setof Pos) (set)]
                [winds : Winds (hash)])
               ([(l row) (in-indexed ls)]
                [(c col) (in-indexed l)])
      (define p (cons row col))
      (match c
        [#\# (values (set-add walls p) winds)]
        [(? Dir? c) (values walls (add-wind winds p c))]
        [#\. (values walls winds)])))
  (values (Ctx rows cols walls (cons (sub1 rows) (- cols 2)) winds) {set (cons 0 1)}))

(: step-winds : Ctx → Ctx)
(define (step-winds ctx)
  (match-define (Ctx rows cols walls tgt winds) ctx)

  (: try : Pos Pos → Pos)
  (define (try pos₁ pos₂) (if (set-member? walls pos₁) pos₂ pos₁))
  
  (define winds*
    (for*/fold ([winds* : Winds (hash)])
               ([(pos dirs) (in-hash winds)]
                [dir (in-list dirs)])
      (match-define (cons row col) pos)
      (define pos*
        (match dir
          [#\^ (try (cons (sub1 row) col)
                    (cons (- rows 2) col))]
          [#\> (try (cons row (add1 col))
                    (cons row 1))]
          [#\< (try (cons row (sub1 col))
                    (cons row (- cols 2)))]
          [#\v (try (cons (add1 row) col)
                    (cons 1 col))]))
      (add-wind winds* pos* dir)))

  (Ctx rows cols walls tgt winds*))

(: step : Ctx State → (Values Ctx State))
(define (step ctx poses)
  (match-define (Ctx rows cols walls tgt winds) ctx)
  (match-define (and ctx* (Ctx _ _ _ _ winds*)) (step-winds ctx))
  (values ctx*
          (for*/set : State ([p (in-set poses)]
                             [row (in-value (car p))]
                             [col (in-value (cdr p))]
                             [p* (in-list (list p
                                                (cons (add1 row) col)
                                                (cons (sub1 row) col)
                                                (cons row (add1 col))
                                                (cons row (sub1 col))))]
                             #:when (<= 0 row (sub1 rows))
                             #:when (<= 0 col (sub1 cols))
                             #:unless (set-member? walls p*)
                             #:unless (hash-has-key? winds* p*))
            p*)))

(: run : Ctx State → (Values Ctx State Integer))
(define (run ctx frontier)
  (match-define (Ctx _ _ _ tgt _) ctx)
  (let loop ([ctx : Ctx ctx]
             [frontier : State frontier]
             [iter : Integer 0])
    (cond
      [(set-member? frontier tgt) (values ctx frontier iter)]
      [else
       (define-values (ctx* frontier*) (step ctx frontier))
       (loop ctx* frontier* (+ 1 iter))])))

(define (q1)
  (parameterize ([input real-input])
    (define-values (ctx state₀) (read-board))
    (define-values (ctx* state* n) (run ctx state₀))
    n))

(define (q2)
  (parameterize ([input real-input])
    (define (Ctx-with-goal [c : Ctx] [goal : Pos])
      (match-define (Ctx rows cols walls _ winds) c)
      (Ctx rows cols walls goal winds))
    (define-values (ctx₀ st₀) (read-board))
    (define start (cons 0 1))
    (define end (Ctx-target ctx₀))
    (define-values (ctx₁ st₁ n₁) (run ctx₀ st₀))
    (define-values (ctx₂ st₂ n₂) (run (Ctx-with-goal ctx₁ start) {set end}))
    (define-values (ctx₃ st₃ n₃) (run (Ctx-with-goal ctx₂ end) {set start}))
    (+ n₁ n₂ n₃)))

(module+ main
  (displayln (q1))
  (displayln (q2)))
