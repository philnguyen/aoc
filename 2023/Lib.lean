import Lean.Data.PersistentHashMap
import Lean.Data.PersistentHashSet

open Lean

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

private def Index.beq : Index n → Index n → Bool :=
  match n with
  | 0 => BEq.beq
  | 1 => BEq.beq
  | _ + 2 => λ ⟨i₀, i⟩ ⟨j₀, j⟩ => i₀ == j₀ && beq i j

instance : BEq (Index n) where beq := Index.beq

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
def Index.straight_adjacents (i : Index n) : List (Index n) :=
  match n with
  | 0 => []
  | 1 => [(i - 1), (i + 1)]
  | _ + 2 => let (i₀, i') := i
             (i₀ - 1, i') ::
             (i₀ + 1, i') ::
             i'.straight_adjacents.map (⟨i₀, ·⟩)

def Index.adjacents (i : Index n) : List (Index n) :=
  let rec go (i : Index n) : List (Index n) :=
    match n with
    | 0 => []
    | 1 => [i - 1, i + 1]
    | m + 2 => let ⟨i₀, i'⟩ := i
               let adjacents' := i'.adjacents
               (i₀ - 1, i') ::
               (i₀ + 1, i') ::
               adjacents'.map (i₀ - 1, ·) ++
               adjacents'.map (i₀, ·) ++
               adjacents'.map (i₀ + 1, ·)
  (go i).filter (· != i)

section Test
  def origin3 : Index 3 := (0, 0, 0)
  example : origin3.straight_adjacents.length = 6 := rfl
  example : [(0, 0, -1), (0, 0, 1), (0, -1, 0), (0, 1, 0), (-1, 0, 0), (1, 0, 0)].all origin3.straight_adjacents.contains
    := rfl

  def origin2 : Index 2 := (0, 0)
  example : origin2.adjacents.length = 8 := rfl
  example : [-1, 1].all $ λ i₀ =>
            [-1, 1].all $ λ i₁ =>
            origin2.adjacents.contains (i₀, i₁)
    := rfl
end Test

def Index.add (v₁ v₂ : Index n) : Index n :=
  match n with
  | 0 => ()
  | 1 => v₁ + v₂
  | _ + 2 => let ⟨n₁, v₁'⟩ := v₁
             let ⟨n₂, v₂'⟩ := v₂
             ⟨n₁ + n₂, add v₁' v₂'⟩


instance : Add (Index n) where
  add := Index.add

abbrev SparseGrid := PersistentHashMap (Index 2)

-----------------------------------------------------------------------
-- IO and strings
-----------------------------------------------------------------------

partial
def IO.FS.Stream.lines (str : IO.FS.Stream): IO (List String) := do
  let l ← str.getLine
  if l.length == 0 then return [] else do let ls ← str.lines; return l.trim :: ls

def stdin_lines : IO (List String) := IO.getStdin >>= IO.FS.Stream.lines

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

def Char.as_digit? (c : Char) : Option ℕ :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else .none

def Char.is_digit : Char → Bool := Option.isSome ∘ as_digit?

section Test
  example : '0'.as_digit? = .some 0 := rfl
  example : '5'.as_digit? = .some 5 := rfl
  example : '9'.as_digit? = .some 9 := rfl
  example : 'a'.as_digit? = .none := rfl
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
-- Set
-----------------------------------------------------------------------

abbrev ℘ (α : Type) [BEq α] [Hashable α] := PersistentHashSet α
notation "⊘" => PersistentHashSet.empty

def ℘.filter [BEq α] [Hashable α] (p : α → Bool) (s : ℘ α) : ℘ α :=
  s.fold (λ s x => if p x then s else s.erase x) s

def ℘.map [BEq α] [Hashable α] [BEq β] [Hashable β] (f : α → β) (s : ℘ α) : ℘ β :=
  s.fold (λ s x => s.insert (f x)) ⊘

def ℘.filterMap [BEq α] [Hashable α] [BEq β] [Hashable β] (f : α → Option β) (s : ℘ α) : ℘ β :=
  s.fold (λ s x => match f x with
                   | .some y => s.insert y
                   | .none => s)
         ⊘

def ℘.union [BEq α] [Hashable α] (s₁ s₂ : ℘ α) : ℘ α :=
  if s₁.size ≤ s₂.size then s₁.fold .insert s₂ else s₂.fold .insert s₁

def ℘.intersect [BEq α] [Hashable α] (s₁ s₂ : ℘ α) : ℘ α :=
  if s₁.size ≤ s₂.size then s₁.filter s₂.contains else s₂.filter s₁.contains

infixl:65 " ∪ " => ℘.union
infixl:70 " ∩ " => ℘.intersect

def List.toSet [BEq α] [Hashable α] : List α → ℘ α := foldl .insert ⊘

-----------------------------------------------------------------------
-- Map
-----------------------------------------------------------------------

infixr:30 " ⊨> " => PersistentHashMap

instance : Hashable Char where
  hash c := c.toNat.toUInt64

def Lean.PersistentHashMap.update [BEq α] [Hashable α] (k : α) (f : α → β → β) (v : β) (m : α ⊨> β) : α ⊨> β :=
  m.insert k (f k (match m.find? k with
                   | .some v => v
                   | .none => v))


def Lean.PersistentHashMap.filter [BEq α] [Hashable α] (p : α → β → Bool) (m : α ⊨> β) : α ⊨> β :=
  m.foldl (λ m k v => if p k v then m else m.erase k) m

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

-----------------------------------------------------------------------
-- Union find
-----------------------------------------------------------------------

structure UnionFind (α : Type) [BEq α] [Hashable α] where
  parents : PersistentHashMap α α
  ranks : PersistentHashMap α ℕ
deriving Inhabited

abbrev UnionFindT (α : Type) [BEq α] [Hashable α] := StateT (UnionFind α)

class MonadUnionFind (α : outParam Type) (m : Type → Type) where
  union : α → α → m Unit
  find : α → m α

private def UnionFind.parent_of [BEq α] [Hashable α] : UnionFind α → α → α
| ⟨parents, _⟩, x => parents.findD x x

private def UnionFind.rank_of [BEq α] [Hashable α] : UnionFind α → α → ℕ
| ⟨_, ranks⟩, x => ranks.findD x 0

def UnionFind.empty [BEq α] [Hashable α] : UnionFind α := ⟨.empty, .empty⟩

partial
def UnionFind.find [Monad m] [BEq α] [Hashable α] (x : α) : (UnionFindT α) m α := do
  let x' := (← get).parent_of x
  if x == x' then return x
  let x₁ ← find x'
  modify (λ uf => {uf with parents := uf.parents.insert x x₁})
  return x₁

def UnionFind.union [Monad m] [BEq α] [Hashable α] (x y : α) : (UnionFindT α) m Unit := do
  let x' ← find x
  let y' ← find y
  if x' != y' then
    let uf@⟨parents, ranks⟩ ← get
    let (x_root, x_root_rank, y_root, y_root_rank) :=
      let x'_rank := uf.rank_of x'
      let y'_rank := uf.rank_of y'
      if x'_rank < y'_rank
        then (y', y'_rank, x', x'_rank)
        else (x', x'_rank, y', y'_rank)
    set $ UnionFind.mk (parents.insert y_root x_root)
                       (if x_root_rank == y_root_rank
                         then ranks.insert x_root (1 + x_root_rank)
                         else ranks)

instance [Monad m] [BEq α] [Hashable α] : MonadUnionFind α (UnionFindT α m) where
  union := UnionFind.union
  find := UnionFind.find
