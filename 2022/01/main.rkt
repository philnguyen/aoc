#lang typed/racket

(define (sum [calories : (Listof Integer)]) : Integer (apply + calories))

(: top : (Listof (Listof Integer)) → Integer)
(define (top calory-lists) (sum (argmax sum calory-lists)))

(: top-3 : (Listof (Listof Integer)) → Integer)
(define (top-3 calory-lists)
  (define top (take ((inst sort (Listof Integer) Integer) calory-lists >= #:cache-keys? #t #:key sum) 3))
  (sum (map sum top)))

(define (read-lists)
  (with-input-from-file "input.txt"
    (λ ()
      (let loop : (Listof (Listof Integer)) ([lists : (Listof (Listof Integer)) '()]
                                             [acc : (Listof Integer) '()])
        (match (read-line)
          [(? eof-object?) lists]
          ["" (loop (cons acc lists) '())]
          [(? string? s) (loop lists (cons (assert (string->number s) exact-integer?) acc))])))))

(module+ main
  (define input (read-lists))
  (printf "Most: ~a~n" (top input))
  (printf "Top 3: ~a~n" (top-3 input)))
