import Lean.Data.PersistentHashMap
import Lean.Data.PersistentHashSet
import Lean.Data.Parsec

open Lean

abbrev ℕ := Nat
abbrev ℤ := Int

-----------------------------------------------------------------------
-- Numbers and counting
-----------------------------------------------------------------------

def Nat.count_by (p : ℕ → Bool) (n : ℕ) : ℕ :=
  n.foldRev (λ i count => if p i then count + 1 else count) 0

section Test
  example : Nat.count_by (· % 2 == 0) 7 = 4 := rfl
end Test

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

def Vec.ref (vec : Vec n t) (i : Index n) : Option t :=
  match n with
  | 0 => vec
  | 1 => match i with
         | .ofNat i => vec.get? i
         | .negSucc _ => .none
  | _ + 2 => let (i₀, i') := i
             match i₀ with
             | .ofNat i₀ => match vec.get? i₀ with
               | .some vec' => vec'.ref i'
               | .none => .none
             | .negSucc _ => .none

section Test
  example : (8 : Vec 0 ℕ).ref () = .some 8 := rfl
  example : Vec.ref (n := 1) ["zero", "one", "two"] 0 = "zero" := rfl
  example : Vec.ref (n := 2) [ ["zero", "one", "two"]
                             , ["foo", "bar", "qux"]
                             ]
                             (1, 1) = .some "bar"
    := rfl
  example : Vec.ref (n := 2) [ ["zero", "one", "two"]
                             , ["foo", "bar", "qux"]
                             ]
                             (3, 3) = .none
    := rfl
  example : Vec.ref (n := 2) [ ["zero", "one", "two"]
                             , ["foo", "bar", "qux"]
                             ]
                             (-3, 3) = .none
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
             ⟨n₁ + n₂, v₁'.add v₂'⟩

def Index.sub (v₁ v₂ : Index n) : Index n :=
  match n with
  | 0 => ()
  | 1 => v₁ - v₂
  | _ + 2 => let ⟨n₁, v₁'⟩ := v₁
             let ⟨n₂, v₂'⟩ := v₂
             ⟨n₁ - n₂, v₁'.sub v₂'⟩

instance : Add (Index n) where add := Index.add
instance : Sub (Index n) where sub := Index.sub

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

def Char.as_digit? (c : Char) : Option ℕ :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else .none

def Char.is_digit : Char → Bool := Option.isSome ∘ as_digit?

section Test
  example : '0'.as_digit? = .some 0 := rfl
  example : '5'.as_digit? = .some 5 := rfl
  example : '9'.as_digit? = .some 9 := rfl
  example : 'a'.as_digit? = .none := rfl
end Test

section Test
  example : ["123", "234", "345"].fold_char (λ | acc, i, '2' => i :: acc
                                               | acc, _, _ => acc)
                                            []
          = [(1, 0), (0, 1)]
    := rfl

  example : ["123", "234", "345"].map_grid (·.as_digit?.getD 0)
          = [[1, 2, 3], [2, 3, 4], [3, 4, 5]]
    := rfl
end Test

-----------------------------------------------------------------------
-- Option
-----------------------------------------------------------------------

instance {α : Type u} {β : Type v} : OfNat (α → Option β) 0 where
  ofNat _ := .none
instance {α : Type u} {β : Type v} : Add (α → Option β) where
  add f g := λ x => match f x with
                    | y@(.some _) => y
                    | .none => g x

-----------------------------------------------------------------------
-- List
-----------------------------------------------------------------------
def List.map_reduce (map : α → β) (reduce : β → β → β) (init : β) : List α → β :=
  foldl (λ acc x => reduce acc (map x)) init
def List.sum_by  [Add α] [OfNat α 0] (f : x → α) := map_reduce f Add.add 0
def List.prod_by [Mul α] [OfNat α 1] (f : x → α) := map_reduce f Mul.mul 1
def List.sum  [Add α] [OfNat α 0] : List α → α := sum_by id
def List.prod [Mul α] [OfNat α 1] : List α → α := prod_by id

def List.count_by (p : α → Bool) (xs : List α) : ℕ :=
  xs.foldl (λ count x => if p x then count + 1 else count) 0

section Test
  example : [2, 3, 4].sum = 9 := rfl
  example : [2, 3, 4].prod = 24 := rfl
  example : [1, 2, 3, 4, 5].count_by (· % 2 == 0) = 2 := rfl
end Test

def List.is_prefix_of [BEq α] : List α → List α → Bool
| [], _ => true
| x :: xs, y :: ys => x == y && xs.is_prefix_of ys
| _, _ => false

section Test
  example : [].is_prefix_of [1] = true := rfl
  example : [1, 2].is_prefix_of [1, 2, 3, 4] = true := rfl
  example : [1, 2].is_prefix_of [2, 3] = false := rfl
  example : [1, 2].is_prefix_of [] = false := rfl
end Test

def List.last! [Inhabited α] : List α → α := head! ∘ reverse
def List.last? : List α → Option α := head? ∘ reverse
def List.lastD (xs : List α) (x : α) : α := xs.reverse.headD x

def List.reduce (op : α → α → α) : List α → Option α
| [] => .none
| x :: xs => .some (xs.foldl op x)

def List.min [Min α] (xs : List α) := xs.reduce Min.min
def List.max [Max α] (xs : List α) := xs.reduce Max.max

-----------------------------------------------------------------------
-- Set
-----------------------------------------------------------------------

prefix:30 "℘" => PersistentHashSet

syntax "#{" term,* "}" : term
macro_rules
| `(#{}) => `(PersistentHashSet.empty)
| `(#{$x:term}) => `(PersistentHashSet.insert .empty $x) -- TODO weird it's needed
| `(#{ $x:term , $xs:term,* }) => `(PersistentHashSet.insert #{$xs,*} $x)

section Test
  example : (#{} : ℘ ℕ).size = 0 := rfl
  example : #{"foo", "bar", "qux"}.size = 3 := rfl
end Test

def Lean.PersistentHashSet.filter [BEq α] [Hashable α] (p : α → Bool) (s : ℘ α) : ℘ α :=
  s.fold (λ s x => if p x then s else s.erase x) s

def Lean.PersistentHashSet.map [BEq α] [Hashable α] [BEq β] [Hashable β] (f : α → β) (s : ℘ α) : ℘ β :=
  s.fold (λ s x => s.insert (f x)) #{}

def Lean.PersistentHashSet.filterMap [BEq α] [Hashable α] [BEq β] [Hashable β] (f : α → Option β) (s : ℘ α) : ℘ β :=
  s.fold (λ s x => match f x with
                   | .some y => s.insert y
                   | .none => s)
         #{}

def Lean.PersistentHashSet.union [BEq α] [Hashable α] (s₁ s₂ : ℘ α) : ℘ α :=
  if s₁.size ≤ s₂.size then s₁.fold .insert s₂ else s₂.fold .insert s₁

def Lean.PersistentHashSet.intersect [BEq α] [Hashable α] (s₁ s₂ : ℘ α) : ℘ α :=
  if s₁.size ≤ s₂.size then s₁.filter s₂.contains else s₂.filter s₁.contains

def Lean.PersistentHashSet.map_reduce [BEq α] [Hashable α] (map : α → β) (reduce : β → β → β) (init : β) : ℘ α → β :=
  fold (λ acc x => reduce acc (map x)) init
def Lean.PersistentHashSet.sum_by  [BEq α] [Hashable α] [Add σ] [OfNat σ 0] (f : α → σ) := map_reduce f Add.add 0
def Lean.PersistentHashSet.prod_by [BEq α] [Hashable α] [Mul π] [OfNat π 1] (f : α → π) := map_reduce f Mul.mul 1
def Lean.PersistentHashSet.sum  [BEq α] [Hashable α] [Add α] [OfNat α 0] : ℘ α → α := sum_by id
def Lean.PersistentHashSet.prod [BEq α] [Hashable α] [Mul α] [OfNat α 1] : ℘ α → α := prod_by id
def Lean.PersistentHashSet.all [BEq α] [Hashable α] (p : α → Bool) := map_reduce p (· && ·) true
def Lean.PersistentHashSet.any [BEq α] [Hashable α] (p : α → Bool) := map_reduce p (· || ·) false

infixl:65 " ∪ " => PersistentHashSet.union
infixl:70 " ∩ " => PersistentHashSet.intersect

def List.toSet [BEq α] [Hashable α] : List α → ℘ α := foldl .insert #{}
def Lean.PersistentHashSet.toList [BEq α] [Hashable α] (xs : ℘ α) : List α :=
  xs.fold (λ acc x => x :: acc) []

instance [BEq α] [Hashable α] : BEq (℘ α) where
  beq xs ys := xs.size == ys.size && xs.all ys.contains

instance [BEq α] [Hashable α] : Hashable (℘ α) where
  hash xs := xs.sum_by hash

instance [BEq α] [Hashable α] [ToString α] : ToString (℘ α) where
  toString xs := "{" ++ xs.fold (λ acc x => acc ++ (if acc.length == 0 then "" else ", ") ++ s!"{x}") "" ++ "}"

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

declare_syntax_cat kv
syntax term " ↦ " term : kv
syntax "#[|" kv,* "]" : term
macro_rules
| `(#[|]) => `(PersistentHashMap.empty)
| `(#[| $k:term ↦ $v:term ]) => `(PersistentHashMap.insert .empty $k $v) -- TODO weird it's needed
| `(#[| $k:term ↦ $v:term, $p:kv,* ]) => `(PersistentHashMap.insert #[| $p,* ] $k $v)

instance [BEq k] [Hashable k] [ToString k] [ToString v] : ToString (k ⊨> v) where
  toString m := "[" ++ m.foldl (λ acc k v => acc ++ (if acc.length == 0 then "" else ", ") ++ s!"{k} ↦ {v}") "" ++ "]"

section Test
  example : (#[|] : ℕ ⊨> ℕ).size = 0 := rfl
  example : #[|"foo" ↦ 42, "bar" ↦ 44, "qux" ↦ 4].size = 3 := rfl
end Test

-----------------------------------------------------------------------
-- Parsing
-----------------------------------------------------------------------

def Lean.Parsec.nat : Parsec ℕ := do
  let digits ← Parsec.many1 Parsec.digit
  return digits.foldl (λ acc d => acc * 10 + d.as_digit?.get!) 0

def Lean.Parsec.int : Parsec ℤ :=
  (attempt $ do skipChar '-'
                return match (← nat) with
                | 0 => 0
                | m + 1 => .negSucc m) <|>
  (.ofNat <$> nat)

def Lean.Parsec.skip_word (s : String): Parsec Unit := ws *> skipString s *> ws

partial
def Lean.Parsec.sep_by (elem : Parsec α) (sep : Parsec β) : Parsec (List α) :=
  (Parsec.attempt $ do
      let a ← elem
      let _ ← sep
      let as ← sep_by elem sep
      return a :: as) <|>
  (Parsec.attempt $ do
      let a ← elem
      return [a]) <|>
  (pure [])

def Lean.Parsec.alts (alts : List (String × α)) : Parsec α :=
  let fail := fail s!"None of {alts.map (λ ⟨s, _⟩ => s)} match"
  (alts.foldl (λ parse ⟨s, a⟩ => parse <|> (attempt $ do skipString s; pure a))
              fail) <|> fail

def Lean.Parsec.run! [Inhabited α] (comp : Parsec α) (s : String) : α := match comp.run s with
  | .ok a => a
  | .error e => panic! e

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

-----------------------------------------------------------------------
-- Memoization
-----------------------------------------------------------------------

abbrev MemoT (k : Type u) (v : Type w) [BEq k] [Hashable k] := StateT (k ⊨> v)

class MonadMemo (k v : outParam Type) (m : Type → Type) where
  run_memoized : k → m v → m v

instance [Monad m] [BEq k] [Hashable k] : MonadMemo k v (MemoT k v m) where
  run_memoized key comp := do
    let memo ← get
    match memo.find? key with
    | .some v => return v
    | .none => let v ← comp
               modify (·.insert key v)
               return v

-----------------------------------------------------------------------
-- Priority Queue
-----------------------------------------------------------------------

-- Leftist heap from Okasaki

inductive Heap (α : Type) :=
| empty : Heap α
| tree : ℕ → α → Heap α → Heap α → Heap α

private def Heap.toString [ToString α] : Heap α → String
| .empty => "[]"
| .tree _ x l r => s!"{x} ∷ {toString l} ∷ {toString r}"

instance [ToString α] : ToString (Heap α) where
  toString := Heap.toString

private def Heap.rank : Heap α → ℕ
| .empty => 0
| .tree r _ _ _ => r

private def Heap.mk_tree (x : α) (a b : Heap α) : Heap α :=
  if rank a ≥ rank b
    then .tree (rank b + 1) x a b
    else .tree (rank a + 1) x b a

partial -- TODO
def Heap.merge [Ord α] : Heap α → Heap α → Heap α
| h, .empty
| .empty, h => h
| h₁@(.tree _ x a₁ b₁), h₂@(.tree _ y a₂ b₂) =>
  match Ord.compare x y with
  | .lt | .eq => mk_tree x a₁ (merge b₁ h₂)
  | _ => mk_tree y a₂ (merge h₁ b₂)

def Heap.insert [Ord α] (x : α) (h : Heap α) := merge (.tree 1 x .empty .empty) h

def Heap.min? : Heap α → Option α
| .empty => .none
| .tree _ x _ _ => .some x

def Heap.min_popped? [Ord α] : Heap α → Option (Heap α)
| .empty => .none
| .tree _ _ a b => merge a b

def Heap.from_list [Ord α] : List α → Heap α := List.foldl (·.insert ·) .empty

-----------------------------------------------------------------------
-- Binary search
-----------------------------------------------------------------------

partial -- TODO
def binary_search [Ord α] (f : ℕ → α) (target : α) (lo_incl hi_incl : ℕ) : Option (ℕ × α) :=
  let rec loop (lo_incl hi_incl : ℕ) : Option (ℕ × α) :=
    if lo_incl > hi_incl then .none
    else let m := (lo_incl + hi_incl) / 2
         let fm := f m
         match Ord.compare target fm with
         | .lt => loop lo_incl (m - 1)
         | .gt => loop (m + 1) hi_incl
         | .eq => .some (m, fm)
  loop lo_incl hi_incl
