import Lib

abbrev Race := ℕ × ℕ -- Time × Distance
abbrev Input := List Race

def sample : Input := [(7, 9), (15, 40), (30, 200)]
def real : Input := [(63, 411), (78, 1274), (94, 2047), (68, 1035)]
def sample2 : Race := (71530, 940200)
def real2 : Race := (63789468, 411127420471035)

def count_beating_ways : Race → ℕ
| ⟨time, distance_to_beat⟩ =>
  let traveled (hold : ℕ) : ℕ := hold * (time - hold)
  time.count_by (traveled · > distance_to_beat)

def prod_beating_ways (races : Input) : ℕ := races.prod_by count_beating_ways

def main : IO Unit := do
  IO.println s!"Q1 on sample: {prod_beating_ways sample}"
  IO.println s!"Q1 on real: {prod_beating_ways real}"
  IO.println s!"Q2 on sample: {count_beating_ways sample2}"
  IO.println s!"Q2 on real: {count_beating_ways real2}"
