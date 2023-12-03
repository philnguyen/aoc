import Lib

private def loop (parse : List Char → Option ℕ) : List Char → List ℕ
| cs@(_ :: cs') => match parse cs with
                   | .some d => d :: loop parse cs'
                   | .none => loop parse cs'
| [] => []

private def List.first_digit? : List Char → Option ℕ
| c :: _ => c.as_digit?
| _ => .none

private def List.first_digit_name? : List Char → Option ℕ
| 'o' :: 'n' :: 'e' :: _               => .some 1
| 't' :: 'w' :: 'o' :: _               => .some 2
| 't' :: 'h' :: 'r' :: 'e' :: 'e' :: _ => .some 3
| 'f' :: 'o' :: 'u' :: 'r' :: _        => .some 4
| 'f' :: 'i' :: 'v' :: 'e' :: _        => .some 5
| 's' :: 'i' :: 'x' :: _               => .some 6
| 's' :: 'e' :: 'v' :: 'e' :: 'n' :: _ => .some 7
| 'e' :: 'i' :: 'g' :: 'h' :: 't' :: _ => .some 8
| 'n' :: 'i' :: 'n' :: 'e' :: _        => .some 9
| _ => .none

def List.parse_q1 := loop first_digit?
def List.parse_q2 := loop (first_digit? + first_digit_name?)

def sum_by (parse_digits : List Char → List ℕ) : IO Unit := do
  let lines ← stdin_lines
  let nums := lines.map (λ l => let ds := parse_digits l.toList
                                ds.head! * 10 + ds.last!)
  IO.println s!"values are {nums}"
  IO.println s!"Their sum is {nums.sum}"

def main : IO Unit := sum_by List.parse_q2
