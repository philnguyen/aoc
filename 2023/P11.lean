import Lib

abbrev Map := List (Index 2)

def remap (scale : ℕ) (inhabited_coords : List ℤ) : ℤ ⊨> ℤ :=
  let rec go (n₀ n₀' : ℤ) (acc : ℤ ⊨> ℤ) : List ℤ → (ℤ ⊨> ℤ)
    | [] => acc
    | n₁ :: ns =>
      let d := n₁ - n₀ - 1
      let n₁' := n₀' + d * scale + 1
      go n₁ n₁' (acc.insert n₁ n₁') ns
  go (-1) (-1) #[|] inhabited_coords

def expand_by_dim (scale : ℕ) (dim : Fin 2) (m : Map) : Map :=
  let inhabited_coords := m |>.map (·.get dim) |>.distinct |>.sorted
  let all_mappings := remap scale inhabited_coords
  m.map (λ idx => idx.set dim (all_mappings.find! (idx.get dim)))

def dist_sum (m : Map) : ℕ := Id.run $ do
  let mut acc := 0
  for idx in m do
    for jdx in m do
      if idx != jdx then
        acc ← acc + idx.manhattan_dist jdx
  return acc / 2

def read_map : IO Map :=
  return (← stdin_lines) |>.map_sparse_grid (λ | '#' => .some ()
                                               | _ => .none)
                         |>.keys

def show_dist_sum (scale : ℕ) : IO Unit := do
  let m := (← read_map) |> expand_by_dim scale 0
                        |> expand_by_dim scale 1
  IO.println s!"Ans: {dist_sum m}"

def q1 := show_dist_sum 2
def q2 := show_dist_sum 1000000

def main : IO Unit := q2
