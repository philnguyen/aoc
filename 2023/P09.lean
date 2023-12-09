import Lib
open Lean

def List.deriv : List ℤ → List ℤ
| [] | [_] =>  []
| x₁ :: x₂ :: xs => (x₂ - x₁) :: (x₂ :: xs).deriv

partial
def List.derivs (l : List ℤ) : List (List ℤ) :=
  if l.all (· == 0) then [l] else l :: l.deriv.derivs

partial
def List.last_num (ls : List (List ℤ)) :=
  let rec go : List (List ℤ) → ℤ
    | [n :: _] => n
    | (n₁ :: _) :: (n₂ :: ns₂) :: ls => go (((n₁ + n₂) :: n₂ :: ns₂) :: ls)
    | _ => panic! "nope!"
  go (ls.map List.reverse).reverse

partial
def List.first_num (ls : List (List ℤ)) :=
  let rec go : List (List ℤ) → ℤ
    | [n :: _] => n
    | (n₁ :: _) :: (n₂ :: ns₂) :: ls => go (((n₂ - n₁) :: n₂ :: ns₂) :: ls)
    | _ => panic! "nope!"
  go ls.reverse

def with_extrap (extrap : List (List ℤ) → ℤ) : IO Unit := do
  let parse_line : Parsec (List ℤ) := Parsec.sep_by Parsec.int Parsec.ws
  let lines := (← stdin_lines).map parse_line.run!
  let anses := lines.map (extrap ·.derivs)
  for ans in lines.zip anses do
    let (n, ns) := ans
    IO.println s!"Line {ns} --> {n}"
  IO.println s!"Sum is {anses.sum}"

def q1 := with_extrap List.last_num
def q2 := with_extrap List.first_num

def main : IO Unit := q1
