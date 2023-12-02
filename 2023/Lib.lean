import Lean.Data.PersistentHashMap
import Lean.Data.PersistentHashSet

open Lean

abbrev ℘ (α : Type) [BEq α] [Hashable α] := PersistentHashSet α
abbrev ℕ := Nat
abbrev ℤ := Int

-----------------------------------------------------------------------
-- Vectors and Matrices
-----------------------------------------------------------------------

abbrev Index : ℕ → Type
| 0 => Unit
| 1 => ℤ -- negative index ok
| n + 1 => ℤ × Index n

abbrev Vec : ℕ → Type → Type
| 0, t => t
| n + 1, t => List (Vec n t)

def Vec.ref (default : t)  (vec : Vec n t) (i : Index n) : t :=
  match n with
  | 0 => vec
  | 1 => match i with
         | .ofNat i => vec.getD i default
         | .negSucc _ => default
  | _ + 2 => let (i₀, i') := i
             match i₀ with
             | .ofNat i₀ => match vec.get? i₀ with
               | .some vec' => vec'.ref default i'
               | .none => default
             | .negSucc _ => default

section Test
  example : (8 : Vec 0 ℕ).ref 0 () = 8 := rfl
  example : Vec.ref (n := 1) "" ["zero", "one", "two"] 0 = "zero" := rfl
  example : Vec.ref (n := 2) "" [ ["zero", "one", "two"]
                                , ["foo", "bar", "qux"]
                                ]
                                (1, 1) = "bar"
    := rfl
  example : Vec.ref (n := 2) "" [ ["zero", "one", "two"]
                                , ["foo", "bar", "qux"]
                                ]
                                (3, 3) = ""
    := rfl
  example : Vec.ref (n := 2) "" [ ["zero", "one", "two"]
                                , ["foo", "bar", "qux"]
                                ]
                                (-3, 3) = ""
    := rfl
end Test

-- `Index 2` interpreted as `row × col` as opposed to `x × y`
abbrev Move n := Index n → Index n
def Move.all_basis_moves : List (Move n) := match n with
  | 0 => []
  | 1 => [(· - 1), (· + 1)]
  | m + 2 => (λ ⟨i₀, i⟩ => (i₀ - 1, i)) ::
             (λ ⟨i₀, i⟩ => (i₀ + 1, i)) ::
             (all_basis_moves (n := m + 1)).map (λ ⟨i₀, i⟩ => ⟨i₀, · i⟩)

def Move.all_moves : List (Move n) := match n with
  | 0 => []
  | 1 => [(· - 1), (· + 1)]
  | m + 2 => let sub_moves := all_moves (n := m + 1)
             sub_moves.map (λ ⟨i₀, i⟩ => ⟨i₀ - 1, · i⟩) ++
             sub_moves.map (λ ⟨i₀, i⟩ => ⟨i₀ + 1, · i⟩)

section Test
  def ex_basis_moves3 := (Move.all_basis_moves (n := 3)).map (· (0, 0, 0))
  example : ex_basis_moves3.length = 6 := rfl
  example : [(0, 0, -1), (0, 0, 1), (0, -1, 0), (0, 1, 0), (-1, 0, 0), (1, 0, 0)].all ex_basis_moves3.contains
    := rfl

  def ex_moves3 := (Move.all_moves (n := 3)).map (· (0, 0, 0))
  example : ex_moves3.length = 8 := rfl
  example : [-1, 1].all $ λ i₀ =>
            [-1, 1].all $ λ i₁ =>
            [-1, 1].all $ λ i₂ =>
            ex_moves3.contains (i₀, i₁, i₂)
    := rfl
end Test

abbrev SparseGrid := PersistentHashMap (Index 2)

-----------------------------------------------------------------------
-- IO and strings
-----------------------------------------------------------------------

partial
def IO.FS.Stream.lines (str : IO.FS.Stream): IO (List String) := do
  let l ← str.getLine
  if l.length == 0 then return [] else do let ls ← str.lines; return l.trim :: ls

def List.map_splitted_lines (f : List String → α) (lines : List String) (sep : String := " ") : List α :=
  lines.map (λ l => f (l.splitOn sep))

@[simp]
def List.fold_line_groups (on_line : α → String → α) (a₀ : α)
                          (on_group : β → α → β    ) (b₀ : β)
                          (lines : List String)
                          : β :=
  let (a, b) := lines.foldl (λ (a, b) l => match l with
                                           | "" => (a₀, on_group b a)
                                           | _ => (on_line a l, b))
                            (a₀, b₀)
  on_group b a

@[simp]
def List.map_line_groups (on_line : String → α) (on_group : List α → β) : List String → List β :=
  fold_line_groups (λ as s => on_line s :: as) [] (λ b as => on_group as :: b) []

@[simp]
def List.fold_char (f : α → Index 2 → Char → α) (a₀ : α) (lines : List String) : α :=
  let (a, _) := lines.foldl
                  (λ (a, row) l =>
                     let (a, _) := l.foldlAux (λ (a, i) c => (f a (row, i) c, i + 1)) ⟨l.length⟩ 0 (a, 0)
                     (a, row + 1))
                  (a₀, 0)
  a

@[simp]
def List.fold_sparse_grid (cell : Char → Option α)
                          (acc : g → Index 2 → α → g)
                          : g → List String → g :=
  fold_char (λ g i c =>
               match cell c with
               | .some a => acc g i a
               | .none => g)

@[simp]
def List.Stream.map_sparse_grid (cell : Char → Option α) : List String → SparseGrid α :=
  fold_sparse_grid cell (λ m i v => m.insert i v) .empty

def List.map_grid (cell : Char → α) : List String → Vec 2 α := map (·.toList.map cell)

section Test
  example : ["123", "234", "345"].fold_char (λ | acc, i, '2' => i :: acc
                                               | acc, _, _ => acc)
                                            []
          = [(1, 0), (0, 1)]
    := rfl
    
  example : ["123", "234", "345"].map_grid (λ | '1' => 1
                                              | '2' => 2
                                              | '3' => 3
                                              | '4' => 4
                                              | '5' => 5
                                              | _ => 0)
          = [[1, 2, 3], [2, 3, 4], [3, 4, 5]]
    := rfl
end Test

-----------------------------------------------------------------------
-- List
-----------------------------------------------------------------------

def List.sum_by [Add α] [OfNat α 0] (f : x → α) := List.foldl (λ acc x => acc + f x) 0
def List.sum [Add α] [OfNat α 0] := List.sum_by id
def List.prod_by [Mul α] [OfNat α 1] (f : x → α) := List.foldl (λ acc x => acc * f x) 1
def List.prod [Mul α] [OfNat α 1] := List.prod_by id

section Test
  example : [2, 3, 4].sum = 9 := rfl
  example : [2, 3, 4].prod = 24 := rfl
end Test

-----------------------------------------------------------------------
-- State search
-----------------------------------------------------------------------

structure Queue (α : Type) where
  front : List α
  back : List α
deriving Repr

@[simp]
 def Queue.empty : Queue α := ⟨[], []⟩

@[simp]
def Queue.insert : α → Queue α → Queue α
| x, ⟨front, back⟩ => ⟨x :: front, back⟩

@[simp]
def Queue.next : Queue α → Option (α × Queue α)
| ⟨front, x :: back⟩ => .some ⟨x, ⟨front, back⟩⟩
| ⟨front, []⟩ => match front.reverse with
                 | x :: back' => .some ⟨x, ⟨[], back'⟩⟩
                 | [] => .none

inductive StepResult s :=
| next : List s → StepResult s
| success : StepResult s

class Scheduler (q : Type → Type) where
  empty : q α
  next : q α → Option (α × q α)
  schedule : List α → q α → q α

instance : Scheduler List where
  empty := []
  next | [] => .none
       | x :: xs => .some (x, xs)
  schedule := List.append

instance : Scheduler Queue where
  empty := Queue.empty
  next := Queue.next
  schedule xs q := xs.foldr .insert q

partial
def search (step : s → StepResult s) (start : s) [Scheduler q] [BEq s] [Hashable s] : Option s :=
  let Cached s [BEq s] [Hashable s] := StateM (℘ s)
  let rec go (alts : q s) : Cached s (Option s) :=
    match Scheduler.next alts with
    | .none => return .none
    | .some (s, alts') =>
      match step s with
      | .next ss => do
        let (ss, seen) :=
          ss.foldl (λ | acc@(ss, seen), s =>
                       if seen.contains s then acc else (s :: ss, seen.insert s))
                   ([], (← get))
        set seen
        go (Scheduler.schedule ss alts')
      | .success => return (.some s)
  go (Scheduler.schedule [start] Scheduler.empty)
    |>.run (PersistentHashSet.empty.insert start)
    |>.fst

def search_dfs [BEq s] [Hashable s] := search (q := List) (s := s)
def search_bfs [BEq s] [Hashable s] := search (q := Queue) (s := s)

section Test
  example : ∃ q, .some (1, q) = Queue.next (.insert 3 (.insert 2 .(.insert 1 .empty)))
    := by simp; exists ⟨[], [2, 3]⟩
end Test
