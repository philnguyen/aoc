import Lib
import Lean.Data.Parsec
import Lean.Data.PersistentHashSet
open Lean

structure Card where
  id : ℕ
  winnings : ℘ ℕ
  haves : ℘ ℕ
deriving Inhabited

instance : ToString Card where
  toString | ⟨id, winnings, haves⟩ => s!"{id}: {winnings} | {haves}"

def Card.parse : Parsec Card := do
  let read_num_list : Parsec (List ℕ) := Array.toList <$> Parsec.many (Parsec.nat <* Parsec.ws)
  Parsec.skip_word "Card"; let id ← Parsec.nat
  Parsec.skip_word ":"   ; let wins ← read_num_list
  Parsec.skip_word "|"   ; let haves ← read_num_list
  return ⟨id, wins.toSet, haves.toSet⟩

def Card.score : Card → ℕ
| ⟨_, winnings, haves⟩ => match (haves ∩ winnings).size with
                          | 0 => 0
                          | n + 1 => 2 ^ n

def Card.score_q2 : Card → ℕ
| ⟨_, winnings, haves⟩ => (winnings ∩ haves).size

partial
def List.play (cards : List Card) : List (ℕ × Card) :=
  let rec bump : ℕ → ℕ → List (ℕ × Card) → List (ℕ × Card)
    | n + 1, d, (c, card) :: cards => (c + d, card) :: bump n d cards
    | _, _, cards => cards
  let rec go : List (ℕ × Card) → List (ℕ × Card)
    | [] => []
    | (n, card) :: cards => (n, card) :: go (bump card.score_q2 n cards)
  go (cards.map (⟨1, ·⟩))

def read_cards : IO (List Card) := do
  let lines ← stdin_lines
  return lines.map Card.parse.run!

def q1 : IO Unit := do
  let cards ← read_cards
  let scores := cards.map Card.score
  for card in cards do
    IO.println s!"{card} worth {card.score}"
  IO.println s!"The scores sum to {scores.sum}"

def q2 : IO Unit := do
  let cards ← read_cards
  let played_cards := cards.play
  for (n, card) in played_cards do
    IO.println s!"{n} of {card} scoring {card.score_q2}"
  IO.println s!"The score is {played_cards.sum_by (·.fst)}"

def main : IO Unit := q2
