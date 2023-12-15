import Lib

abbrev Map := ℘ (Index 2) × ℘ (Index 2) × ℤ × ℤ -- rounds × sharps × num_rows × num_cols

def move (dir : Index 2) : Map → Map
| (rounds, sharps, rows, cols) =>
  let in_bound : Index 2 → Bool | ⟨r, c⟩ => 0 ≤ r ∧ r < rows ∧ 0 ≤ c ∧ c < cols
  let rounds' := rounds |>.toList
                        |>.sorted_by (λ pos₁ pos₂ => (pos₂.sub pos₁).dot dir < 0)
                        |>.foldl (λ rounds' pos => Id.run $ do
                                    let mut pos := pos
                                    let mut pos' := pos.add dir
                                    while in_bound pos' ∧ ¬ rounds'.contains pos' ∧ ¬ sharps.contains pos' do
                                      pos := pos'
                                      pos' := pos'.add dir
                                    rounds'.insert pos)
                                 ∅
  (rounds', sharps, rows, cols)

def move_north := move (-1,  0)
def move_west  := move ( 0, -1)
def move_south := move ( 1,  0)
def move_east  := move ( 0,  1)
def cycle := move_east ∘ move_south ∘ move_west ∘ move_north

def weight : Map → ℤ
| (rounds, _, n, _) => rounds.sum_by (λ ⟨r, _⟩ => n - r)

def read_map : IO Map := do
  let lines ← stdin_lines
  let rounds := lines |>.indices_where (. == 'O') |>.toSet
  let sharps := lines |>.indices_where (. == '#') |>.toSet
  return (rounds, sharps, lines.length, lines.head!.length)

def main := do
  let m ← read_map
  IO.println s!"q1: {weight (move_north m)}"
  IO.println s!"q2: {weight (cached_iter 1000000000 cycle m)}"
