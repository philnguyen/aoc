import Lib
open Lean

abbrev CubeSet := ℕ

abbrev Color := ℕ
abbrev Color.red := 2
abbrev Color.green := 3
abbrev Color.blue := 5

abbrev cube_set (counts : List (Color × ℕ)) : CubeSet := counts.prod_by (λ ⟨color, count⟩ => color ^ count)

abbrev bag : CubeSet := cube_set [(.red, 12), (.green, 13), (.blue, 14)]

structure Game where
  id : ℕ
  sets : List CubeSet
deriving Inhabited

instance : ToString Game where
  toString | ⟨id, _⟩ => ToString.toString id

def Game.is_possible (g : Game) (s : CubeSet) : Bool := g.sets.all (s % · == 0)

def Game.parse : Parsec Game :=
  let id : Parsec ℕ := do
    Parsec.skipString "Game "
    let id ← Parsec.nat
    Parsec.skipString ": "
    return id
  let component : Parsec (Color × ℕ) := do
    let count ← Parsec.nat
    Parsec.skipChar ' '
    let color ← Parsec.alts [("red", .red), ("green", .green), ("blue", .blue)]
    return (color, count)
  let cubeSet : Parsec CubeSet := cube_set <$> Parsec.sep_by component (Parsec.skipString ", ")
  let cubeSets : Parsec (List CubeSet) := Parsec.sep_by cubeSet (Parsec.skipString "; ")
  Game.mk <$> id <*> cubeSets

partial
def CubeSet.power (s : CubeSet) : ℕ :=
  -- poor life choice lol
  let rec count_color (s : CubeSet) (color : Color) : ℕ :=
    if s % color == 0 then 1 + (count_color (s / color) color) else 0
  [.red, .green, .blue].prod_by (count_color s ·)

def read_games : IO (List Game) := do
  let lines ← (← IO.getStdin).lines
  return lines.map (λ l => match Game.parse.run l with
                           | .ok game => game
                           | .error e => panic! e)

def q1 : IO Unit := do
  let games ← read_games
  let valid_games := games.filter (·.is_possible bag)
  let id_sum := (valid_games.map Game.id).sum
  IO.println s!"Valid games are {valid_games}"
  IO.println s!"Their sum is {id_sum}"

def q2 : IO Unit := do
  let lcm (n₁ n₂ : ℕ) : ℕ := n₁ * n₂ / n₁.gcd n₂
  let games ← read_games
  let powers := games.map (λ g => CubeSet.power (g.sets.foldl lcm 1))
  let sum := powers.sum
  IO.println s!"The powers are {powers}"
  IO.println s!"Their sum is {sum}"

def main : IO Unit := q2
