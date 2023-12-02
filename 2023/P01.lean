import Lib

private def loop (parse : List Char → Option ℕ) : List Char → List ℕ
| cs@(_ :: cs') => match parse cs with
                   | .some d => d :: loop parse cs'
                   | .none => loop parse cs'
| [] => []

def List.parse_digits := loop $
  λ | '1' :: _ => .some 1
    | '2' :: _ => .some 2
    | '3' :: _ => .some 3
    | '4' :: _ => .some 4
    | '5' :: _ => .some 5
    | '6' :: _ => .some 6
    | '7' :: _ => .some 7
    | '8' :: _ => .some 8
    | '9' :: _ => .some 9
    | _ => .none

def List.parse_digits' := loop $
  λ | '1' :: _
    | 'o' :: 'n' :: 'e' :: _               => .some 1
    | '2' :: _
    | 't' :: 'w' :: 'o' :: _               => .some 2
    | '3' :: _
    | 't' :: 'h' :: 'r' :: 'e' :: 'e' :: _ => .some 3
    | '4' :: _
    | 'f' :: 'o' :: 'u' :: 'r' :: _        => .some 4
    | '5' :: _
    | 'f' :: 'i' :: 'v' :: 'e' :: _        => .some 5
    | '6' :: _
    | 's' :: 'i' :: 'x' :: _               => .some 6
    | '7' :: _
    | 's' :: 'e' :: 'v' :: 'e' :: 'n' :: _ => .some 7
    | '8' :: _
    | 'e' :: 'i' :: 'g' :: 'h' :: 't' :: _ => .some 8
    | '9' :: _
    | 'n' :: 'i' :: 'n' :: 'e' :: _        => .some 9
    | _ => .none

def sum_by (parse_digits : List Char → List ℕ) : IO Unit := do
  let lines ← (← IO.getStdin).lines
  let nums := lines.map (λ l => let ds := parse_digits l.toList
                                let d₁ := ds.head!
                                let d₂ := ds.reverse.head!
                                d₁ * 10 + d₂)
  let sum := nums.sum
  IO.println s!"values are {nums}"
  IO.println s!"Their sum is {sum}"

def main : IO Unit := sum_by List.parse_digits'
