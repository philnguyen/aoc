import Lib

abbrev Map := ℘ (Index 2) × ℘ (Index 2) × ℤ × ℤ -- rounds × sharps × num_rows × num_cols

def read_map : IO Map := do
  let lines ← stdin_lines
  let m := lines.map_sparse_grid (λ | 'O' => false
                                    | '#' => true
                                    | _ => .none)
  let rounds := m.keys.filter (m.find? · == .some false) |>.toSet
  let sharps := m.keys.filter (m.find? · == .some true ) |>.toSet
  return (rounds, sharps, lines.length, lines.head!.length)

def shift (dim : Fin 2) (target : ℤ) (m : Map) : Map :=
  let (rounds, sharps, rows, cols) := m
  let rounds' := rounds |>.toList
                        |>.sorted_by (λ pos₁ pos₂ => (target - pos₁.get dim).natAbs < (target - pos₂.get dim).natAbs)
                        |>.foldl (λ rounds' pos =>
                                    let x := pos.get dim
                                    let pos' := pos.set dim (if x > target then x - 1 else x + 1)
                                    rounds'.insert (if x = target ∨ rounds.contains pos' ∨ sharps.contains pos' then pos else pos'))
                                 ∅
  (rounds', sharps, rows, cols)

def shift_north : Map → Map                  := shift 0 0
def shift_west  : Map → Map                  := shift 1 0
def shift_south : Map → Map | m@⟨_, _, r, _⟩ => shift 0 (r - 1) m
def shift_east  : Map → Map | m@⟨_, _, _, c⟩ => shift 1 (c - 1) m
def cycle := fix shift_east ∘ fix shift_south ∘ fix shift_west ∘ fix shift_north

def Map.weight : Map → ℤ
| (rounds, _, n, _) => rounds.sum_by (λ ⟨r, _⟩ => n - r)

def main := do
  let m ← read_map
  IO.println s!"q1: {(fix shift_north m).weight}"
  IO.println s!"q2: {(cached_iter 1000000000 cycle m).weight}"
