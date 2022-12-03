#lang typed/racket

(require bnf
         "../../utils.rkt")

(File-Path . ≜ . (Listof String))
(State . ::= . (State [current : File-Path]
                      [direct-sizes : (HashTable File-Path Integer)]
                      [tree : (HashTable File-Path (Setof String))]))
(Event . ::= . #f
               (Cd String)
               (Child-Dir [dir : String])
               (Size [name : String] [size : Integer]))

(: accum : String State → State)
(define (accum line st)
  (match-define (State path sizes tree) st)
  (match (string-split line)
    [(list "$" "ls") st]
    [(list "$" "cd" "..") (State (rest path) sizes tree)]
    [(list "$" "cd" "/") (State '() sizes tree)]
    [(list "$" "cd" s) (State (cons s path) sizes tree)]
    [(list "dir" s)
     (State path
            sizes
            ((inst hash-update File-Path (Setof String))
             tree path
             (λ (children) (set-add children s))
             set))]
    [(list (app string->number (? exact-integer? n)) name)
     (State path
            (hash-set sizes (cons name path) n)
            tree)]))

(define (dir-sizes) : (HashTable File-Path Integer)
  (define file-sizes (State-direct-sizes (foldl accum (State '() (hash) (hash))
                                                (file->lines "input.txt"))))
  (for*/fold ([acc : (HashTable File-Path Integer) (hash)])
             ([(file-path size) (in-hash file-sizes)]
              [parent (in-list (tails (rest file-path)))])
    ((inst hash-update File-Path Integer) acc parent (λ (n) (+ n size)) (λ () 0))))

(define (q1)
  (apply + (filter (within #f 100000) (hash-values (dir-sizes)))))

(define (q2)
  (let ([dir-sizes (dir-sizes)])
    (define occupied (hash-ref dir-sizes '()))
    (define free (- 70000000 occupied))
    (define need-more (- 30000000 free))
    (apply min (filter (within need-more #f) (hash-values dir-sizes)))))

(module+ main
  (displayln (q1))
  (displayln (q2)))
