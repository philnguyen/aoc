import Lib
import Lean.Data.Parsec
open Lean

abbrev Map := String ⊨> String × String
inductive Dir := | l | r

def Dir.step (d : Dir) (src : String) (m : Map) : String :=
  let (left, right) := m.find! src
  match d with
  | .l => left
  | .r => right

private def String.ends_with (s : String) (c : Char) : Bool := s.toList.last? == .some c

partial
def run (init : String) (done : String → Bool) (m : Map) (dirs : List Dir) : ℕ :=
  let rec go (acc : ℕ) (cur : String) : List Dir → ℕ
    | [] => go acc cur dirs
    | d :: ds => let next := d.step cur m
                 let acc' := acc + 1
                 if done next then acc' else go acc' next ds
  go 0 init dirs

def run_many (m : Map) (ds : List Dir) : ℕ :=
  m |>.toList
    |>.map (λ ⟨k, _⟩ => k)
    |>.filter (·.ends_with 'A')
    |>.map_reduce (run · (·.ends_with 'Z') m ds) Nat.lcm 1

def with_runner [ToString α] (run : Map → List Dir → α) : IO Unit := do
  let parseDirs : Parsec (List Dir) :=
    return (← Parsec.many1 (Parsec.alts [("L", Dir.l), ("R", Dir.r)])).toList
  let parse_seg (m : Map) : Parsec Map := do
    let word : Parsec String := do
      let cs ← Parsec.many1 (Parsec.satisfy (λ c => '0' ≤ c ∧ c ≤ '9' ∨ 'A' ≤ c ∧ c ≤ 'Z'))
      pure cs.toList.asString
    let src ← word; Parsec.skip_word "= ("
    let l   ← word; Parsec.skip_word ","
    let r   ← word
    return m.insert src (l, r)
  match (← stdin_lines) with
  | dirs :: _ :: segs =>
    let ds := parseDirs.run! dirs
    let m := segs.foldl (λ m l => (parse_seg m).run! l) #[|]
    let steps := run m ds
    IO.println s!"Needed {steps} steps"
  | _ => panic! "BS input"

def q1 := with_runner (run "AAA" (· == "ZZZ"))
def q2 := with_runner run_many

def main : IO Unit := q1
