import Lib
open Lean

inductive Tile := | «|» | «-» | «⌞» | «⌟» | «⌝» | «⌜» | «⋆»
  deriving Repr, Inhabited, BEq, Hashable
open Tile
derive_ToString Tile

abbrev Cell := Index 2 × Tile
abbrev Map := SparseGrid Tile

def Index.above   : Index 2 → Index 2 → Bool | ⟨r₁, c₁⟩, ⟨r₂, c₂⟩ => c₁ == c₂ ∧ r₁ + 1 == r₂
def Index.left_of : Index 2 → Index 2 → Bool | ⟨r₁, c₁⟩, ⟨r₂, c₂⟩ => r₁ == r₂ ∧ c₁ + 1 == c₂

def Tile.connects : Tile → Index 2 → Index 2 → Bool
| «|», (r₁, c₁), (r₂, c₂) => c₁ == c₂ ∧ (r₁ - r₂).natAbs == 1
| «-», (r₁, c₁), (r₂, c₂) => r₁ == r₂ ∧ (c₁ - c₂).natAbs == 1
| «⌞», i, j => i.left_of j ∨ j.above i
| «⌟», i, j => j.left_of i ∨ j.above i
| «⌝», i, j => j.left_of i ∨ i.above j
| «⌜», i, j => i.left_of j ∨ i.above j
| «⋆», _, _ => true

def connects: Index 2 × Tile → Index 2 × Tile → Bool
| ⟨idx₁, «⋆»  ⟩, ⟨idx₂, tile₂⟩ => tile₂.connects idx₂ idx₁
| ⟨idx₁, tile₁⟩, ⟨idx₂, «⋆»  ⟩ => tile₁.connects idx₁ idx₂
| ⟨idx₁, tile₁⟩, ⟨idx₂, tile₂⟩ => tile₁.connects idx₁ idx₂ ∧ tile₂.connects idx₂ idx₁

example : connects ((1, 1), «⋆») ((1, 2), «-») = true := rfl
example : connects ((1, 2), «-») ((1, 3), «⌝») = true := rfl
example : connects ((2, 2), «|») ((3, 2), «⌟») = true := rfl
example : connects ((3, 2), «-») ((3, 1), «⌞») = true := rfl
example : connects ((1, 2), «-») ((0, 2), «|») = false := rfl
example : connects ((109, 28), «⋆») ((109, 29), «⌟») = true := rfl
example : connects ((109, 28), «⋆») ((108, 28), «⌟») = false := rfl

-- Run bfs, returning visited positions as well as farthest distance traveled
partial
def bfs (m : Map) (touched : ℘ (Index 2)) (frontier : ℘ Cell) (dist : ℕ) : (ℕ × ℘ (Index 2)) :=
  if frontier.size == 0 then (dist - 1, touched)
  else let (touched', frontier') :=
         frontier.fold (λ acc cell@⟨idx, _⟩ =>
                           idx.straight_adjacents.foldl
                             (λ acc@⟨touched, frontier⟩ idx' =>
                                if touched.contains idx' then acc
                                else match m.find? idx' with
                                     | .some tile' =>
                                       if connects cell (idx', tile')
                                       then (touched.insert idx', frontier.insert (idx', tile'))
                                       else acc
                                     | .none => acc)
                             acc)
                        (touched, #{})
       bfs m touched' frontier' (dist + 1)

-- Read map, returning it along with bfs result
def map_bfs : IO (List String × Map × ℕ × ℘ (Index 2)) := do
  let lines ← stdin_lines
  let the_map := lines.map_sparse_grid (λ | '|' => «|»
                                          | '-' => «-»
                                          | 'L' => «⌞»
                                          | 'J' => «⌟»
                                          | '7' => «⌝»
                                          | 'F' => «⌜»
                                          | 'S' => «⋆»
                                          | '.' => .none
                                          | c => panic s!"Nope: {c}")
  let start_index := the_map.toList |>.find? (λ ⟨_, v⟩ => v == «⋆») |>.get! |>.fst
  return (lines, the_map, bfs the_map #{start_index} #{(start_index, «⋆»)} 0)

def q1 : IO Unit := do
  let (_, _, farthest, _) ← map_bfs
  IO.println s!"Answer : {farthest}"

def q2 : IO Unit := do
  let (lines, the_map, _, the_loop) ← map_bfs
  let (region_counts, _) : (Bool ⊨> ℘ (Index 2)) × (ℤ ⊨> Bool) :=
    -- For each row, alternates out/in every time passing through loop's wall
    lines.fold_char (λ | acc@⟨counts, io⟩, idx@⟨r, _⟩, _ =>
                         let mode := io.findD r false
                         let io' := io.insert r !mode
                         let counts' := counts.collect mode idx
                         if ¬ the_loop.contains idx then (counts', io)
                         else match the_map.find? idx with
                              | .some «|» | .some «⌞» | .some «⌟» => (counts, io')
                              | .some _ => acc
                              | .none => (counts', io))
                    (#[|], #[|])
  IO.println s!"Total ins: {(region_counts.findD true #{}).size}"

def main : IO Unit := q2
