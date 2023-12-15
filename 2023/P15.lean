import Lib
open Lean

def HASH (s : String) : ℕ := s.toList.foldl (λ acc c => (acc + c.toNat) * 17 % 256) 0

abbrev Elem := String × ℕ

inductive Cmd :=
| move : Elem → Cmd
| remove : String → Cmd
deriving Inhabited

abbrev State := ℕ ⊨> List Elem

def Elem.has_label : String → Elem → Bool | s, ⟨box, _⟩ => box == s

def q1 : List String → ℕ := List.sum_by HASH

def q2 (commands : List String) : ℕ :=
  let interp (st : State) : Cmd → State
  | .move elem@(label, _) =>
    let box := HASH label
    let elems := st.findD box []
    st.insert box $ match elems.find? (Elem.has_label label) with
                    | .some elem₀ => elems.replace elem₀ elem
                    | .none => elem :: elems
  | .remove label =>
    st.update (HASH label) (λ _ elems => elems.filter (¬ ·.has_label label)) []

  let sum (st : State) : ℕ :=
    let rec sum_elems (box : ℕ) (ith : ℕ) : List Elem → ℕ
      | [] => 0
      | ⟨_, x⟩ :: elems => box * ith * x + sum_elems box (ith + 1) elems
    st |>.toList
       |>.sum_by (λ ⟨box, elems⟩ => sum_elems (box + 1) 1 elems.reverse)

  commands |>.map (λ s => match s.splitOn "=" with
                          | [box, val] => Cmd.move (box, val.toNat!)
                          | _ => match s.splitOn "-" with
                                 | [val, ""] => Cmd.remove val
                                 | s => panic! s!"Invalid: {s}")
           |>.foldl interp #[|]
           |> sum

def main : IO Unit := do
  let commands := (← stdin_lines).head!.splitOn ","
  IO.println s!"q1: {q1 commands}"
  IO.println s!"q2: {q2 commands}"
