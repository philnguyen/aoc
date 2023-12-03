import Lib
import Lean.Data.PersistentHashSet
import Lean.Data.PersistentHashMap
open Lean

private def List.fold_nums (on_num : α → ℕ → List (Index 2) → α) (init : α) (lines : List String) : α :=
  let (acc, acc_num, idxs) :=
    lines.fold_char (λ | ⟨acc, acc_num, acc_idxs⟩, idx, c =>
                         match c.as_digit? with
                         | .some d => (acc, acc_num * 10 + d, idx :: acc_idxs)
                         | .none => (on_num acc acc_num acc_idxs, 0, []))
                    (init, 0, [])
  if idxs == [] then on_num acc acc_num idxs else acc

def q1 : IO Unit := do
  let lines ← stdin_lines

  let symbol_ajacents : (℘ (Index 2)):=
    lines.fold_sparse_grid
      (λ c => if c == '.' || c.is_digit then .none else some ())
      (λ idxs idx _ => idx.adjacents.foldl .insert idxs)
      #{}

  let nums := lines.fold_nums (λ nums num idxs => if idxs.any symbol_ajacents.contains then num :: nums else nums) []
  IO.println s!"Nums are {nums},\n summing to {nums.sum}"

def q2 : IO Unit := do
  let lines ← stdin_lines

  let gear_index : Index 2 ⊨> Index 2 :=
    lines.fold_sparse_grid
      (if · == '*' then .some () else .none)
      (λ idxs idx _ => idx.adjacents.foldl (λ idxs p => idxs.insert p idx) idxs)
      #[|]

  let gear_nums : Index 2 ⊨> List ℕ :=
    lines.fold_nums
      (λ gear_nums num idxs =>
         let gears_to_add := (idxs.filterMap gear_index.find?).toSet
         gears_to_add.fold (λ gear_nums gear => gear_nums.update gear (λ _ => (num :: ·)) []) gear_nums)
      #[|]

  let valid_gear_nums := gear_nums.filter (λ _ ns => ns.length == 2)
  let sum := valid_gear_nums.toList.sum_by (λ ⟨_, ls⟩ => ls.prod)
  IO.println s!"nums are {valid_gear_nums.toList}"
  IO.println s!"summing to {sum}"

def main := q2
