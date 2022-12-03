#lang typed/racket

(require bnf
         unreachable)

(require/typed "input.rkt"
  [real-input (Listof Sexp)]
  [test-input (Listof Sexp)])

(Exp . ::= . Integer
             (App [op : Symbol] [l : Exp] [r : Exp])
             #f)
(Comp . ≜ . (→ Exp))
(Env . ≜ . (Mutable-HashTable Symbol Comp))

(define input : (Parameterof (Listof Sexp)) (make-parameter test-input))

(: parse-line : Env Sexp → Void)
(define (parse-line env l)
  (match l
    [`(humn ,_) (hash-set! env 'humn (λ () #f))]
    [`(root ,(? symbol? l) ,_ ,(? symbol? r)) (hash-set! env 'root (λ () (App '= ((hash-ref env l)) ((hash-ref env r)))))]
    [`(,(? symbol? x) ,(? exact-integer? n)) (hash-set! env x (λ () n))]
    [`(,(? symbol? x) ,(? symbol? l) ,(? symbol? op) ,(? symbol? r))
     (define (lift [★ : (Integer Integer → Integer)]) : (Exp Exp → Exp)
       (match-lambda**
        [((? integer? n) (? integer? m)) (★ n m)]
        [(l r) (App op l r)]))
     (define ★
       (lift (match op
               ['+ +]
               ['- -]
               ['* *]
               ['/ quotient])))
     (hash-set! env x (λ () (★ ((hash-ref env l)) ((hash-ref env r)))))]))

(: solve-eq : Exp Integer → Integer)
(define (solve-eq e n)
  (match e
    [#f n]
    [(App '+ e₁ e₂)
     (cond [(integer? e₁) (solve-eq e₂ (- n e₁))]
           [(integer? e₂) (solve-eq e₁ (- n e₂))])]
    [(App '- e₁ e₂)
     (cond [(integer? e₁) (solve-eq e₂ (- e₁ n))]
           [(integer? e₂) (solve-eq e₁ (+ e₂ n))])]
    [(App '* e₁ e₂)
     (cond [(integer? e₁) (solve-eq e₂ (quotient n e₁))]
           [(integer? e₂) (solve-eq e₁ (quotient n e₂))])]
    [(App '/ e₁ e₂)
     (cond [(integer? e₁) (solve-eq e₂ (quotient e₁ n))]
           [(integer? e₂) (solve-eq e₁ (* e₂ n))])]))

(define (solve)
  (define env : Env (make-hasheq))
  (for ([l (in-list (input))])
    (parse-line env l))
  (match-define (App '= l r) ((hash-ref env 'root)))
  (cond [(integer? l) (solve-eq r l)]
        [(integer? r) (solve-eq l r)]))

(module+ main
  (parameterize ([input real-input])
    (solve)))
