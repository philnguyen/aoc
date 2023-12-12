import Lib
open Lean

inductive Elem := | «?» | «#» | «.» deriving BEq, Hashable
open Elem

abbrev Input := List Elem × List ℕ
  
mutual
  def count_matches : Input → MemoT Input ℕ Id ℕ
  | input@(e :: es, n :: ns) => MonadMemo.run_memoized input $ do
    let skip_cases  := count_matches (es, n :: ns)
    let match_cases := count_matches_given_n n (e :: es) ns
    match e with
    | «.» => skip_cases
    | «#» => match_cases
    | «?» => return (← skip_cases) + (← match_cases)
  | (es, []) => return if es.any (· == «#») then 0 else 1
  | ([], _ ) => return 0
  
  def count_matches_given_n : ℕ → List Elem → List ℕ → MemoT Input ℕ Id ℕ
  | n + 1, «#» :: es, ns
  | n + 1, «?» :: es, ns => count_matches_given_n n es ns
  | _ + 1, «.» :: _ , _
  | _ + 1, []       , _
  | 0    , «#» :: _ , _  => return 0
  | 0    , «?» :: xs, ns
  | 0    , «.» :: xs, ns => count_matches (xs, ns)
  | 0    , []       , ns => return if ns == [] then 1 else 0
end
termination_by
  count_matches input => input
  count_matches_given_n _ es ns => (es, ns)

def read_input : IO (List Input) := do
  let parse_line : Parsec Input := do
    let elems ← Parsec.many1 (Parsec.alts [("?", «?»), ("#", «#»), (".", «.»)])
    Parsec.ws
    let nats ← Parsec.sep_by Parsec.nat (Parsec.skipString ",")
    return (elems.toList, nats)
  return (← stdin_lines).map parse_line.run!
  
def main : IO Unit := do
  let rows_q1 ← read_input
  let rows_q2 := rows_q1.map λ ⟨es, ns⟩ =>
               ( es ++ [«?»] ++ es ++ [«?»] ++ es ++ [«?»] ++ es ++ [«?»] ++ es
               , ns ++ ns ++ ns ++ ns ++ ns
               )
  let run_count_matches (input : Input) : ℕ := (count_matches input).run' #[|]
  IO.println s!"q1 : {rows_q1.sum_by run_count_matches}"
  IO.println s!"q2 : {rows_q2.sum_by run_count_matches}"
