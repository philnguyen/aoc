import Lean.Data.PersistentHashMap
import Lean.Data.PersistentHashSet
import Lean.Data.Parsec

open Lean

abbrev ℕ := Nat
abbrev ℤ := Int

-----------------------------------------------------------------------
-- Debugging
-----------------------------------------------------------------------

macro "derive_ToString" t:term : command =>
  `(instance : ToString $t where toString := Std.Format.pretty ∘ repr)

-----------------------------------------------------------------------
-- Ordering
-----------------------------------------------------------------------

private inductive Ordered (s : Type) where
| mk : [Ord t] → (s → t) → Ordered s

private def compare_by {s : Type} : List (Ordered s) → s → s → Ordering
| [], _, _ => .eq
| Ordered.mk prop :: props, s₁, s₂ =>
  match compare (prop s₁) (prop s₂) with
  | .eq => compare_by props s₁ s₂
  | o => o

macro "derive_Ord" t:term "by" os:term,* : command =>
  `(instance : Ord $t where compare := compare_by [$[Ordered.mk $os],*])

def List.lexi_compare [Ord α] : List α → List α → Ordering
| x :: xs, y :: ys => match compare x y with
                      | .eq => xs.lexi_compare ys
                      | o => o
| [], _ :: _ => .lt
| _ :: _, [] => .gt
| [], [] => .eq

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

private def Fin.zero_absurd {α : Type u} (i : Fin 0) : α := by
  have ⟨_, hi⟩ := i; have := Nat.not_lt_zero; contradiction

def Index.get (idx : Index n) (i : Fin n) : ℤ :=
  match n with
  | 0 => Fin.zero_absurd i
  | 1 => idx
  | m + 2 => let (idx₀, idx') := idx
             match i with
             | 0 => idx₀
             | ⟨j + 1, hj⟩ => idx'.get ⟨j, by simp_arith [Nat.lt_of_succ_lt_succ] at *; assumption⟩

def Index.set (idx : Index n) (i : Fin n) (v : ℤ) : Index n :=
  match n with
  | 0 => Fin.zero_absurd i
  | 1 => v
  | m + 2 => let (idx₀, idx') := idx
             match i with
             | 0 => (v, idx')
             | ⟨j + 1, hj⟩ => ⟨idx₀, idx'.set ⟨j, by simp_arith [Nat.lt_of_succ_lt_succ] at *; simp_arith [hj]⟩ v⟩

def Index.compare_at : List (Fin n) → Index n → Index n → Ordering
| [], _, _ => .eq -- arbitrary
| i :: is, idx, jdx => match compare (idx.get i) (jdx.get i) with
                       | .eq => compare_at is idx jdx
                       | o => o

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

def Vec.upd [Inhabited t] (vec : Vec n t) (i : Index n) (f : t → t) : Vec n t :=
  match n with
  | 0 => f vec
  | 1 => match i with
         | .ofNat i => vec.set i (f (vec.get! i))
         | .negSucc _ => vec
  | _ + 2 => let (i₀, i') := i
             match i₀ with
             | .ofNat i₀ => match vec.get? i₀ with
               | .some vec' => vec.set i₀ (vec'.upd i' f)
               | .none => vec
             | .negSucc _ => vec

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

  example : Index.get (n := 3) (1, 2, 3) 2 = 3 := rfl
  example : Index.set (n := 3) (1, 2, 3) 2 42 = (1, 2, 42) := rfl
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

def Index.manhattan_dist (i j : Index n) : ℕ := match n with
| 0 => 0
| 1 => (i - j).natAbs
| _ + 2 => let ⟨i₀, i'⟩ := i
           let ⟨j₀, j'⟩ := j
           (i₀ - j₀).natAbs + i'.manhattan_dist j'

def Index.pointwise (op : ℤ → ℤ → ℤ) (v₁ v₂ : Index n) : Index n :=
  match n with
  | 0 => ()
  | 1 => op v₁ v₂
  | _ + 2 => let ⟨n₁, v₁'⟩ := v₁
             let ⟨n₂, v₂'⟩ := v₂
             ⟨op n₁ n₂, pointwise op v₁' v₂'⟩

def Index.add : Index n → Index n → Index n := pointwise (· + ·)
def Index.sub : Index n → Index n → Index n := pointwise (· - ·)
instance : Add (Index n) where add := Index.add
instance : Sub (Index n) where sub := Index.sub

-- It's `map`, but due to type-aliasing, name it `pointwise` to avoid confusion with `List.map`
def Vec.pointwise (f : α → β) (v : Vec n α) : Vec n β := match n with
| 0     => f v
| _ + 1 => v.map (pointwise f) 

def Vec.pointwise2 (f : α₁ → α₂ → β) (v₁ : Vec n α₁) (v₂ : Vec n α₂) : Vec n β := match n with
| 0 => f v₁ v₂
| _ + 1 => List.zipWith (pointwise2 f) v₁ v₂

abbrev SparseGrid := PersistentHashMap (Index 2)

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
  example : Index.manhattan_dist (n := 3) (0, 1, 2) (3, 4, 5) = 9 := rfl

  example : Index.add (n := 3) (1, 2, 3) (4, 5, 6) = (5, 7, 9) := rfl

  example : Vec.pointwise (n := 2) toString [[1, 2, 3], [2, 3, 4]] = [["1", "2", "3"], ["2", "3", "4"]] := rfl
  example : Vec.pointwise2 (n := 1) (· * ·) [2, 3, 4] [5, 6, 7] = [10, 18, 28] := rfl
end Test

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
  reverse ∘ fold_line_groups (λ as s => on_line s :: as) [] (λ b as => on_group as.reverse :: b) []

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
def List.map_sparse_grid (cell : Char → Option α) : List String → SparseGrid α :=
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

  example : ["123", "234", "", "abc", "foo", "bar"].map_line_groups String.toList id =
            [ [['1', '2', '3'], ['2', '3', '4']]
            , [['a', 'b', 'c'], ['f', 'o', 'o'], ['b', 'a', 'r']]
            ] :=
    rfl
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
def List.sum_by  [Add α] [OfNat α 0] (f : x → α) : List x → α := map_reduce f Add.add 0
def List.prod_by [Mul α] [OfNat α 1] (f : x → α) : List x → α := map_reduce f Mul.mul 1
def List.sum  [Add α] [OfNat α 0] : List α → α := sum_by id
def List.prod [Mul α] [OfNat α 1] : List α → α := prod_by id

def List.count_by (p : α → Bool) (xs : List α) : ℕ :=
  xs.foldl (λ count x => if p x then count + 1 else count) 0

def List.is_prefix_of [BEq α] : List α → List α → Bool
| [], _ => true
| x :: xs, y :: ys => x == y && xs.is_prefix_of ys
| _, _ => false

def List.last! [Inhabited α] : List α → α := head! ∘ reverse
def List.last? : List α → Option α := head? ∘ reverse
def List.lastD (xs : List α) (x : α) : α := xs.reverse.headD x

def List.reduce (op : α → α → α) : List α → Option α
| [] => .none
| x :: xs => .some (xs.foldl op x)
def List.reduce! [Inhabited α] (op : α → α → α) : List α → α := Option.get! ∘ reduce op

def List.min [Min α] (xs : List α) := xs.reduce Min.min
def List.max [Max α] (xs : List α) := xs.reduce Max.max

def List.replace_all [BEq α] (a b : α) : List α → List α
| a₁ :: as => (if a == a₁ then b else a₁) :: replace_all a b as
| [] => []

def List.sorted_by (l : List α) (prec : α → α → Bool) := (l.toArray.qsort prec).toList
def List.sorted_with (l : List α) (cmp : α → α → Ordering) := l.sorted_by (match cmp · · with
                                                                           | .lt | .eq => true
                                                                           | .gt => false)
def List.sorted [Ord α] (l : List α) := l.sorted_with compare

def List.foldl_with_index (f : β → α → ℕ → β) (acc : β) (xs : List α) : β :=
  (xs.foldl (λ | ⟨ac, i⟩, x => (f ac x i, i + 1)) (acc, 0)).fst

section Test
  example : [2, 3, 4].sum = 9 := rfl
  example : [2, 3, 4].prod = 24 := rfl
  example : [1, 2, 3, 4, 5].count_by (· % 2 == 0) = 2 := rfl

  example : [].is_prefix_of [1] = true := rfl
  example : [1, 2].is_prefix_of [1, 2, 3, 4] = true := rfl
  example : [1, 2].is_prefix_of [2, 3] = false := rfl
  example : [1, 2].is_prefix_of [] = false := rfl

  example : [1, 2, 3, 2, 1].replace_all 2 5 = [1, 5, 3, 5, 1] := rfl
end Test

-----------------------------------------------------------------------
-- Set
-----------------------------------------------------------------------

prefix:70 "℘" => PersistentHashSet

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

def Lean.PersistentHashSet.partition [BEq α] [Hashable α] (p : α → Bool) (s : ℘ α) : ℘ α × ℘ α :=
  s.fold (λ ⟨t, f⟩ x => if p x then (t.insert x, f) else (t, f.insert x)) (#{}, #{})

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
def Lean.PersistentHashSet.sum_by  [BEq α] [Hashable α] [Add σ] [OfNat σ 0] (f : α → σ) : ℘ α → σ := map_reduce f Add.add 0
def Lean.PersistentHashSet.prod_by [BEq α] [Hashable α] [Mul π] [OfNat π 1] (f : α → π) : ℘ α → π := map_reduce f Mul.mul 1
def Lean.PersistentHashSet.sum  [BEq α] [Hashable α] [Add α] [OfNat α 0] : ℘ α → α := sum_by id
def Lean.PersistentHashSet.prod [BEq α] [Hashable α] [Mul α] [OfNat α 1] : ℘ α → α := prod_by id
def Lean.PersistentHashSet.all [BEq α] [Hashable α] (p : α → Bool) := map_reduce p (· && ·) true
def Lean.PersistentHashSet.any [BEq α] [Hashable α] (p : α → Bool) := map_reduce p (· || ·) false

infixl:65 " ∪ " => PersistentHashSet.union
infixl:70 " ∩ " => PersistentHashSet.intersect

def List.toSet [BEq α] [Hashable α] : List α → ℘ α := foldl .insert #{}
def Lean.PersistentHashSet.toList [BEq α] [Hashable α] (xs : ℘ α) : List α :=
  xs.fold (λ acc x => x :: acc) []
def List.distinct [BEq α] [Hashable α] (xs : List α) : List α := xs.toSet.toList
def Lean.PersistentHashSet.some_elem! [BEq α] [Hashable α] [Inhabited α] (xs : ℘ α) : α := xs.toList.head!

instance [BEq α] [Hashable α] : BEq (℘ α) where
  beq xs ys := xs.size == ys.size && xs.all ys.contains

instance [BEq α] [Hashable α] : Hashable (℘ α) where
  hash xs := xs.sum_by hash

instance [BEq α] [Hashable α] [ToString α] : ToString (℘ α) where
  toString xs := "{" ++ xs.fold (λ acc x => acc ++ (if acc.length == 0 then "" else ", ") ++ s!"{x}") "" ++ "}"

instance [Hashable l] [Hashable r] : Hashable (l ⊕ r) where
  hash | .inl l => hash l
       | .inr r => hash r * 31

-----------------------------------------------------------------------
-- Map
-----------------------------------------------------------------------

infixr:34 " ⊨> " => PersistentHashMap

instance : Hashable Char where
  hash c := c.toNat.toUInt64

def Lean.PersistentHashMap.update [BEq α] [Hashable α] (k : α) (f : α → β → β) (v : β) (m : α ⊨> β) : α ⊨> β :=
  m.insert k (f k (match m.find? k with
                   | .some v => v
                   | .none => v))

def Lean.PersistentHashMap.filter [BEq α] [Hashable α] (p : α → β → Bool) (m : α ⊨> β) : α ⊨> β :=
  m.foldl (λ m k v => if p k v then m else m.erase k) m

def Lean.PersistentHashMap.collect [BEq α] [Hashable α] [BEq β] [Hashable β]
                                   (m : α ⊨> ℘ β) (a : α) (b : β) : α ⊨> ℘ β :=
  m.insert a ((m.findD a #{}).insert b)

def Lean.PersistentHashMap.collect_list [BEq α] [Hashable α]
                                        (m : α ⊨> List β) (a : α) (b : β) : α ⊨> List β :=
  m.insert a (b :: m.findD a [])

def Lean.PersistentHashMap.count_up [BEq α] [Hashable α]
                                    [Add n] [OfNat n 0] [OfNat n 1]
                                    (m : α ⊨> n) (a : α) : α ⊨> n :=
  m.insert a (1 + m.findD a 0)

def Lean.PersistentHashMap.keys [BEq α] [Hashable α] (m : α ⊨> β) : List α := m.toList.map Prod.fst
def Lean.PersistentHashMap.vals [BEq α] [Hashable α] (m : α ⊨> β) : List β := m.toList.map Prod.snd

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
-- Numbers and counting
-----------------------------------------------------------------------

def Nat.count_by (p : ℕ → Bool) (n : ℕ) : ℕ :=
  n.foldRev (λ i count => if p i then count + 1 else count) 0

def List.tally [BEq α] [Hashable α] (xs : List α) : α ⊨> ℕ :=
  xs.foldl (λ m x => m.insert x (1 + m.findD x 0)) #[|]

def Nat.lcm (a b : ℕ) : ℕ := a * b / a.gcd b

section Test
  example : Nat.count_by (· % 2 == 0) 7 = 4 := rfl
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

partial
def bfs [BEq s] [Hashable s]
        (start : s)
        (step : s → List s)
        (init : α)
        (acc : α → (s ⊨> List s) → α) : α :=
  let rec iter  (queued : ℘ s) (res : α) (front : List s) : α := Id.run $ do
    let mut front' := #[|]
    let mut queued := queued
    for src in front do
      for tgt in step src do
        if ¬ queued.contains tgt then
          queued ← queued.insert tgt
          front' ← front'.collect_list src tgt
    if front'.size > 0 then
      let res' := acc res front'
      let front'' := front'.toList.foldr (λ ⟨_, ss⟩ ss' => ss ++ ss') []
      iter queued res' front''
    else res
  iter #{start} init [start]

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

def Heap.merge [Ord α] : Heap α → Heap α → Heap α
| h, .empty
| .empty, h => h
| h₁@(.tree _ x a₁ b₁), h₂@(.tree _ y a₂ b₂) =>
  match compare x y with
  | .lt | .eq => mk_tree x a₁ (merge b₁ h₂)
  | _ => mk_tree y a₂ (merge h₁ b₂)
termination_by Heap.merge h₁ h₂ => [h₁, h₂]

def Heap.insert [Ord α] (x : α) (h : Heap α) := merge (.tree 1 x .empty .empty) h

def Heap.min? [Ord α] : Heap α → Option (α × Heap α)
| .empty => .none
| .tree _ x a b => .some (x, merge a b)

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
         match compare target fm with
         | .lt => loop lo_incl (m - 1)
         | .gt => loop (m + 1) hi_incl
         | .eq => .some (m, fm)
  loop lo_incl hi_incl

-----------------------------------------------------------------------
-- Function compositions
-----------------------------------------------------------------------

partial
def fix [BEq α] (f : α → α) (x : α) : α :=
  let x' := f x
  if x' == x then x else fix f x'

def iter : ℕ → (α → α) → (α → α)
| 0    , _, x => x
| n + 1, f, x => iter n f (f x)

-- Return `fⁿ x`, knowing `f` has a period that's much smaller than `iters`
def cached_iter [BEq α] [Hashable α] (n : ℕ) (f : α → α) (x : α) : α := Id.run $ do
  let mut distincts : α ⊨> ℕ := #[|]
  let mut x := x
  let mut cycle_end := 0
  let mut cycle_length := 0
  for i in [0 : n] do
    match distincts.find? x with
    | .some i₀ => cycle_length := i - i₀
                  cycle_end := i
                  break
    | .none => distincts := distincts.insert x i
    x := f x
  if cycle_length > 0 then
    for _ in [0 : (n - cycle_end) % cycle_length] do
      x := f x
  return x

section Test
  example : iter 0 f x = x := rfl
  example : iter 1 f x = f x := rfl
  example : iter 3 f x = f (f (f x)) := rfl
end Test
