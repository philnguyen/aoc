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

def move (dim : Fin 2) (target : ℤ) (m : Map) : Map :=
  let (rounds, sharps, rows, cols) := m
  let nudge (pos : Index 2) : Index 2 :=
    let x := pos.get dim
    pos.set dim (if x > target then x - 1 else x + 1)
  let rounds' := rounds |>.toList
                        |>.sorted_by (λ pos₁ pos₂ => (target - pos₁.get dim).natAbs < (target - pos₂.get dim).natAbs)
                        |>.foldl (λ rounds' pos => Id.run $ do
                                    let mut pos := pos
                                    let mut pos' := nudge pos
                                    while pos.get dim != target ∧ ¬ rounds'.contains pos' ∧ ¬ sharps.contains pos' do
                                      pos := pos'
                                      pos' := nudge pos'
                                    rounds'.insert pos)
                                 ∅
  (rounds', sharps, rows, cols)

def move_north : Map → Map                  := move 0 0
def move_west  : Map → Map                  := move 1 0
def move_south : Map → Map | m@⟨_, _, r, _⟩ => move 0 (r - 1) m
def move_east  : Map → Map | m@⟨_, _, _, c⟩ => move 1 (c - 1) m
def cycle := move_east ∘ move_south ∘ move_west ∘ move_north

def Map.weight : Map → ℤ
| (rounds, _, n, _) => rounds.sum_by (λ ⟨r, _⟩ => n - r)

def main := do
  let m ← read_map
  IO.println s!"q1: {(move_north m).weight}"
  IO.println s!"q2: {(cached_iter 1000000000 cycle m).weight}"
