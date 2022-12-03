#lang typed/racket

(require bnf
         unreachable
         "../../utils.rkt"
         "demo.rkt"
         "input.rkt")

(define input : (Parameterof (Vectorof Integer)) (make-parameter test-input))

(define (solve [iters : Integer] [decryption-key : Integer])
  (define N (vector-length (input)))
  (define in
    (for/vector : (Vectorof (Boxof Integer)) ([n (in-vector (input))])
      (box (* decryption-key n))))
  (define 0-key : (Boxof Integer) (box 0))
  (define index->value
    (for/hasheq : (HashTable Integer (Boxof Integer)) ([(bᵢ i) (in-indexed in)])
      (when (zero? (unbox bᵢ))
        (set! 0-key bᵢ))
      (values i bᵢ)))
  (define value->index 
    (for/hasheq : (HashTable (Boxof Integer) Integer) ([(bᵢ i) (in-indexed in)])
      (values bᵢ i)))

  (define (next [v : Integer] [i : Integer]) : Integer
    (cond [(<= 0 v) (remainder (+ v i) N)]
          [else (modulo (+ (sub1 (modulo v N)) i) N)]))

  (: swap :
     (HashTable Integer (Boxof Integer))
     (HashTable (Boxof Integer) Integer)
     Integer Integer →
     (Values (HashTable Integer (Boxof Integer))
             (HashTable (Boxof Integer) Integer)))
  (define (swap vs is i j)
    (define vᵢ (hash-ref vs i))
    (define vⱼ (hash-ref vs j))
    (values (hash-set (hash-set vs i vⱼ) j vᵢ)
            (hash-set (hash-set is vᵢ j) vⱼ i)))
  
  (define-values (out-values out-indices)
    (for*/fold ([vs : (HashTable Integer (Boxof Integer)) index->value]
                [is : (HashTable (Boxof Integer) Integer) value->index])
               ([_ (in-range iters)]
                [_ (in-value (let ()
                               (printf "~n")
                               (for ([i (in-range N)])
                                 (printf "~a " (unbox (hash-ref vs i))))
                               (printf "~n")))]
                [bᵢ (in-vector in)])
      (define dᵢ (remainder (unbox bᵢ) N))
      (define i (hash-ref is bᵢ))
      (cond
        [(< 0 dᵢ)
         (for/fold ([vs vs] [is is]) ([d (in-range 0 dᵢ 1)])
           (swap vs is (modulo (+ i d) N) (modulo (+ i d 1) N)))]
        [(< dᵢ 0)
         (for/fold ([vs vs] [is is]) ([d (in-range 0 dᵢ -1)])
           (swap vs is (modulo (+ i d) N) (modulo (+ i d -1) N)))]
        [else (values vs is)])))

  (let ([0-index (hash-ref out-indices 0-key)])
    (define (ref [i : Integer]) (unbox (hash-ref out-values (remainder (+ i 0-index) N))))
    (+ (ref 1000) (ref 2000) (ref 3000))))

(define (q1)
  (solve 1 1))

(define (q2)
  (parameterize (#;[input real-input])
    (solve 10 811589153)))

(module+ main
  (displayln (q1))
  (displayln (q2)))
