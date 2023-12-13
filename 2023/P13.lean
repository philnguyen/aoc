import Lib
open Lean

abbrev Cell := Bool
abbrev Pattern := Vec 2 Cell

def same [BEq α] (l r : List α) : Bool := List.zipWith (· == ·) l r |>.and

def symm_indices [BEq α] (xs : List α) : ℘ ℕ :=
  let rec go : ℕ → List α → List α → ℘ ℕ
    | _, _ , []
    | _, [], _ => ∅
    | n, ls, rs@(r::rs') => go (n + 1) (r :: ls) rs' ∪ if same ls rs then #{n} else ∅
  match xs with
  | [] => ∅
  | x :: xs' => go 1 [x] xs'

def find_symm (p : Pattern) : ℘ (ℕ ⊕ ℕ) :=
  let on_rows := p |> symm_indices |>.map .inl
  let on_cols := p |>.map symm_indices |>.reduce! (· ∩ ·)  |>.map .inr
  on_rows ∪ on_cols

def find_symm_flipped_one (p : Pattern) : ℘ (ℕ ⊕ ℕ) := Id.run $ do
  let res₀ := (find_symm p).some_elem! -- Assume there's just 1??
  for r in [0:p.length] do
    for c in [0:p.head!.length] do
      let res := find_symm (p.upd (r, c) (¬ .)) |>.erase res₀
      if res.size > 0 then return res
  panic! s!"No smudge???"

def summarize (pats : List Pattern) (find_symm_indices : Pattern → ℘ (ℕ ⊕ ℕ)) : ℕ :=
  pats.sum_by (match · |> find_symm_indices |>.some_elem! with
               | .inl n => 100 * n
               | .inr n => n)

def main : IO Unit := do
  let pats := (← stdin_lines).map_line_groups (· |>.toList |>.map (· == '#')) id
  IO.println s!"q1: {summarize pats find_symm}"
  IO.println s!"q2: {summarize pats find_symm_flipped_one}"
