import Lib

inductive Rank := | n1 | n2 | n3 | n4 | n5 | n6 | n7 | n8 | n9 | t | j | q | k | a
deriving Ord, BEq, Hashable, Inhabited, Repr

inductive Strength := | high | one_pair | two_pairs | three | full_house | four | five
deriving Ord, Inhabited, Repr

derive_ToString Rank
derive_ToString Strength

instance : Ord (List Rank) where compare := List.lexi_compare

abbrev RawHand := List Rank × ℕ
abbrev Hand := Strength × RawHand
derive_Ord Hand by (·.1), (·.2.1)
derive_Ord (Rank × ℕ) by (·.2)

def classify_ranks (maps : Rank ⊨> ℕ) : Strength :=
  match maps.toList.sorted.reverse with
  | [(_, 5)] => .five
  | [(_, 4), (_, 1)] => .four
  | [(_, 3), (_, 2)] => .full_house
  | [(_, 3), (_, 1), (_, 1)] => .three
  | [(_, 2), (_, 2), (_, 1)] => .two_pairs
  | [(_, 2), (_, 1), (_, 1), (_, 1)] => .one_pair
  | [(_, 1), (_, 1), (_, 1), (_, 1), (_, 1)] => .high
  | _ => panic! "Unexpected list {ranks}"

def optimize_jokers (ranks : List Rank) : Rank ⊨> ℕ :=
  let (jokers, normals) := ranks.partition (· == .j)
  let normal_count := normals.tally
  let rec subst_joker (acc : Rank ⊨> ℕ) : List (Rank × ℕ) → ℕ → (Rank ⊨> ℕ)
    | _, 0 => acc
    | [], _ => acc.insert .j 5 -- 5 jokers
    | (c, n) :: cs, n_jokers =>
      if n + n_jokers ≤ 5 then acc.insert c (n + n_jokers)
      else subst_joker (acc.insert c 5) cs (n_jokers - (5 - n))
  subst_joker normal_count normal_count.toList.sorted.reverse jokers.length

def Char.toRank : Char → Rank
| '2' => Rank.n2
| '3' => .n3
| '4' => .n4
| '5' => .n5
| '6' => .n6
| '7' => .n7
| '8' => .n8
| '9' => .n9
| 'T' => .t
| 'J' => .j
| 'Q' => .q
| 'K' => .k
| 'A' => .a
| c => panic! s!"unknown rank {c}"

def with_processing (count_up : List Rank → Rank ⊨> ℕ) (massage : List Rank → List Rank) : IO Unit := do
  let ranked_hands := (← stdin_lines).map (λ l => match l.splitOn " " with
                                                  | [hand, bid] =>
                                                    let ranks := hand.toList.map Char.toRank
                                                    (classify_ranks (count_up ranks), massage ranks, bid.toNat!)
                                                  | _ => panic! s!"hand {l}")
  let sorted_hands := ranked_hands.sorted
  for hand in sorted_hands do
    IO.println s!"{hand}"
  let sum := sorted_hands.foldl_with_index (λ | acc, ⟨_, _, bid⟩, i => acc + (i + 1) * bid) 0
  IO.println s!"Sum is {sum}"

def q1 := with_processing List.tally id
def q2 := with_processing optimize_jokers (·.replace_all .j .n1)

def main : IO Unit := q2
