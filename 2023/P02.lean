import Lib

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

def Game.parse (l : String) : Game :=
  let parse_color : String → Color
      | "red" => .red
      | "green" => .green
      | "blue" => .blue
      | s => panic s!"invalid color {s}"
  let parse_count (str : String) : (Color × ℕ) := match str.trim.splitOn " " with
      | [count, color] => (parse_color color, count.toNat!)
      | _ => panic s!"invalid count string {str}"
  let parse_cube_set (str : String) : CubeSet := cube_set $ (str.trim.splitOn ",").map parse_count
  match l.splitOn ":" with
  | [game, rest] =>
    match game.trim.splitOn " " with
    | [_, id] => Game.mk id.toNat! (rest |>.splitOn ";"
                                         |>.map parse_cube_set)
    | _ => panic "invalid"
  | _ => panic "invalid"

partial


def CubeSet.power (s : CubeSet) : ℕ :=
  -- poor life choice lol
  let rec count_color (s : CubeSet) (color : Color) : ℕ :=
    if s % color == 0 then 1 + (count_color (s / color) color) else 0
  [.red, .green, .blue].prod_by (count_color s ·)

def read_games : IO (List Game) := do
  let lines ← (← IO.getStdin).lines
  return lines.map Game.parse

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

def main : IO Unit := q1
