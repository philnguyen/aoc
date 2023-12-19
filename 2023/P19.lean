import Lib
open Lean

-----------------------------------------
-- Generic semantics
-----------------------------------------
abbrev Var := String
abbrev Instr := String

inductive State :=
| next (instruction : Instr)
| done (accepted : Bool)
deriving Inhabited

class Semantics (m : Type → Type) extends Monad m where
  lt : Var → ℕ → m Bool
  gt : Var → ℕ → m Bool

abbrev Prog m [Semantics m] := Instr ⊨> m State

partial -- Returns whether input accepted
def eval [Semantics m] (prog : Prog m) : m Bool :=
  let rec run (i : Instr) : m Bool := do
    match (← prog.find! i) with
    | .next i' => run i'
    | .done accepted => return accepted
  run "in"


-----------------------------------------
-- q1: concrete execution
-----------------------------------------
abbrev Env := String ⊨> ℕ
abbrev Exec := ReaderM Env

instance : Semantics Exec where
  lt x n := return (← read).find! x < n
  gt x n := return (← read).find! x > n


-----------------------------------------
-- q2: symbolic execution
-----------------------------------------
abbrev SymEnv := String ⊨> ℕ × ℕ
abbrev SymExec := StateT SymEnv List
def SymEnv.size (ρ : SymEnv) : ℕ := ρ.vals.prod_by (λ (lo, hi) => hi - lo + 1)

-- TODO: No idea if Lean's library has a monad-transformer for non-determinism, so hard-coded below
instance : Monad List where
  pure x := [x]
  bind := List.bind
def choices (branches : List (SymExec α)) : SymExec α := λ s => branches.bind (· s)

def refine (x : Var) (lo hi : ℕ) : SymExec Unit := modify (·.insert x (lo, hi))

instance : Semantics SymExec where
  lt x n := do
    let (lo, hi) := (← get).find! x
    if n < lo then choices []
    else if lo ≤ n ∧ n ≤ hi then
      choices [do refine x lo (n - 1); return true,
               do refine x n  hi     ; return false]
    else return true
  gt x n := do
    let (lo, hi) := (← get).find! x
    if n < lo then return true
    else if lo ≤ n ∧ n ≤ hi then
      choices [do refine x (n + 1) hi; return true,
               do refine x lo      n ; return false]
    else choices []


-----------------------------------------
-- Generic parser
-----------------------------------------

open Parsec
def word : Parsec String := return (← many1 asciiLetter).toList.asString

def parse_default [Semantics m] : Parsec (m State) :=
  return match (← word) with
  | "R" => return .done false
  | "A" => return .done true
  | instr => return .next instr

def parse_cond [Semantics m] : Parsec (m State → m State) := do
  let lhs ← word
  let op ← alts [("<", Semantics.lt), (">", Semantics.gt)]
  let rhs ← nat; skipString ":"
  let thn ← parse_default; skipString ","
  return (do if (← op lhs rhs) then thn else ·)

def parse_instr [Semantics m] : Parsec (String × m State) := do
  let id ← word; skipString "{"
  let conds ← many1 (attempt parse_cond)
  let default ← parse_default
  return (id, conds.foldr (λ cond on_false => cond on_false) default)

def parse_asn : Parsec (Var × ℕ) := do
  let x ← word; skipString "="
  let n ← nat
  return (x, n)

def parse_env : Parsec Env := do
  skipString "{"
  let clauses ← sep_by parse_asn (skipString ",")
  return clauses.foldl (λ ρ (k, v) => ρ.insert k v) #[|]

def parse_input [Semantics m] (lines : List String) : Prog m × List Env := Id.run $ do
  let mut prog : Prog m := #[|]
  let mut envs : List Env := []
  for l in lines do
    if let .ok (instruction, semantics) := parse_instr.run l then
      prog := prog.insert instruction semantics
    else if let .ok env := parse_env.run l then
      envs := env :: envs
  return (prog, envs.reverse)


-----------------------------------------
-- Main
-----------------------------------------

def q1 (prog : Prog Exec) (envs : List Env) : ℕ :=
  envs |>.filterM (eval prog) |>.sum_by (·.vals.sum)

def q2 (prog : Prog SymExec) : ℕ :=
  let rng := (1, 4000)
  eval prog |>.run #[| "x" ↦ rng, "m" ↦ rng, "a" ↦ rng, "s" ↦ rng ]
            |>.sum_by (λ (accepted, ρ) => if accepted then ρ.size else 0)

def main : IO Unit := do
  let lines ← stdin_lines
  IO.println s!"q1: {let (prog, envs) := parse_input lines; q1 prog envs}"
  IO.println s!"q2: {let (prog, _   ) := parse_input lines; q2 prog}"
