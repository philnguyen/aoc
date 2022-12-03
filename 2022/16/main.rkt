#lang typed/racket

(require bnf
         unreachable
         "../../utils.rkt")

(Id . ≜ . Symbol)
(Entry . ::= . (Entry [rate : Integer] [nexts : (Listof Id)]))
(Route . ≜ . (List Id Integer (Listof Id)))
(State . ::= . (State [acc : Integer]
                      [current : Id]
                      [remaining-targets : (Setof Id)]
                      [remaining-time : Integer]))

(define test-input : (Listof Route)
  '((AA 0 (DD II BB))
    (BB 13 (CC AA))
    (CC 2 (DD BB))
    (DD 20 (CC AA EE))
    (EE 3 (FF DD))
    (FF 0 (EE GG))
    (GG 0 (FF HH))
    (HH 22 (GG))
    (II 0 (AA JJ))
    (JJ 21 (II))))

(define the-input : (Listof Route)
  '((TN 0 (IX ZZ))
    (DS 0 (IF OU))
    (OP 0 (UH ZQ))
    (FS 0 (IF UH))
    (WO 0 (IS RW))
    (KQ 0 (SI WZ))
    (IX 0 (IF TN))
    (OU 0 (EB DS))
    (ZZ 10 (II GR HA BO TN))
    (OW 0 (RI IS))
    (DV 0 (FR MT))
    (ZK 0 (WG VE))
    (XB 0 (WG HM))
    (XC 0 (IS MT))
    (KO 0 (NH AA))
    (RN 0 (AA MT))
    (ZQ 5 (MF LK OP))
    (MF 0 (ZQ BH))
    (HA 0 (LK ZZ))
    (GB 0 (KZ RW))
    (KZ 24 (GB RI))
    (TC 0 (SI AA))
    (II 0 (SI ZZ))
    (EZ 0 (DF MT))
    (LK 0 (HA ZQ))
    (DU 0 (NH IU))
    (MT 3 (EZ XC RN DV RU))
    (GR 0 (SX ZZ))
    (SX 0 (UH GR))
    (BO 0 (ZZ AO))
    (WG 16 (FR MX XB ZK))
    (IP 8 (HM RU WZ IU))
    (RI 0 (OW KZ))
    (NP 0 (WN EB))
    (IF 19 (IX DS VX FS))
    (AA 0 (RN KO TC MX))
    (IS 15 (OW WO XC))
    (BH 11 (MF))
    (SI 4 (KQ II TC))
    (WN 0 (UH NP))
    (RW 18 (WO GB))
    (DF 0 (NH EZ))
    (WZ 0 (KQ IP))
    (HM 0 (XB IP))
    (VX 0 (AO IF))
    (MX 0 (AA WG))
    (NH 13 (VE KO DU DF))
    (RU 0 (MT IP))
    (IU 0 (IP DU))
    (VE 0 (ZK NH))
    (FR 0 (WG DV))
    (AO 21 (BO VX))
    (EB 22 (OU NP))
    (UH 12 (WN OP SX FS))))

(define input : (Parameterof (Listof Route)) (make-parameter test-input))

(define (solve)
  (define rates
    (for/hasheq : (HashTable Id Integer) ([l (in-list (input))])
      (match-define (list id rate nexts) l)
      (values id rate)))

  (define entries-left
    (for/hasheq : (HashTable Id (Listof Id)) ([l (in-list (input))])
      (match-define (list id rate nexts) l)
      (values id nexts)))

  (define step : (Id → (HashTable Id Integer))
    (let ([memo : (Mutable-HashTable Id (HashTable Id Integer)) (make-hasheq)])
      (λ (src)
        (hash-ref!
         memo
         src
         (λ ()
           (let loop : (HashTable Id Integer)
                ([steps : Integer 1]
                 [visited : (Setof Id) (seteq src)]
                 [frontier : (Setof Id) (list->seteq (hash-ref entries-left src))]
                 [acc : (HashTable Id Integer) (hasheq)])

             (cond
               [(set-empty? frontier) acc]
               [else
                (define acc*
                  (for/fold ([acc : (HashTable Id Integer) acc])
                            ([n (in-set frontier)]
                             #:unless (set-member? visited n))
                    (hash-set acc n steps)))
                (define frontier*
                  (for*/fold ([acc : (Setof Id) (seteq)])
                             ([f (in-set frontier)]
                              [n (in-list (hash-ref entries-left f))]
                              #:unless (set-member? visited n))
                    (set-add acc n)))
                (loop (+ 1 steps) (set-union visited frontier) frontier* acc*)])
             ))))))

  (: flow : Integer Id → Integer)
  (define (flow remaining door) (* remaining (hash-ref rates door)))

  (define targets
    (for/fold ([acc : (Setof Id) (seteq)])
              ([l (in-list (input))] #:when (> (second l) 0))
      (set-add acc (first l))))

  (: loop : (Listof State) (HashTable (Setof Id) Integer) → (HashTable (Setof Id) Integer))
  (define (loop candidates dones)
    (begin
      (printf "~a candidates~n" (length candidates)))
    (cond
      [(null? candidates) (begin0 dones
                            (printf "  Best is ~a~n" (apply max (hash-values dones))))]
      [else
       (define (upd [m : (HashTable (Setof Id) Integer)] [ids : (Setof Id)] [n : Integer])
         (hash-update m ids (λ ([n₀ : Integer]) (max n₀ n)) (λ () 0)))
       (define-values (candidates* dones*)
         (for/fold ([candidates* : (Listof State) '()]
                    [dones* : (HashTable (Setof Id) Integer) dones])
                   ([c (in-list candidates)])
           (match c
             [(State acc cur rem-tgts rem-time)
              (cond
                [(set-empty? rem-tgts)
                 (values candidates* (upd dones* rem-tgts acc))]
                [else
                 (values (for/fold ([candidates* : (Listof State) candidates*])
                                   ([(next steps) (step cur)]
                                    #:when (<= (+ 1 steps) rem-time)
                                    #:when (set-member? rem-tgts next))
                           (define rem-time* (- rem-time (+ 1 steps)))
                           (cons
                            (State (+ acc (* rem-time* (hash-ref rates next)))
                                   next
                                   (set-remove rem-tgts next)
                                   rem-time*)
                            candidates*))
                         (upd dones* rem-tgts acc))])])))

       (loop candidates* dones*)]))

  (define N (quotient (set-count targets) 2))
  (define try-1 (loop (list (State 0 'AA targets 26)) (hash)))
  (printf "now elephant's turn~n")
  (define candidates*
    (for/list : (Listof State) ([(rem-tgts acc) (in-hash try-1)])
      (State acc 'AA rem-tgts 26)))
  (define try-2 (loop candidates* (hash)))

  (apply max (hash-values try-2)))

(module+ main
  (time (parameterize ([input the-input])
    (solve))))
