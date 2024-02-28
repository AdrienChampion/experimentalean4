import Pfds.Init


/-! # Chapter 3 -/
namespace Pfds.C3



/-! ## Leftist heaps -/



/-- Leftist heap structure, where the top of the heap is always the `Ord`-smallest element.

Nodes contain their `Nat` *rank*, which is the length of the right-most branch of the node. Leftist
heaps (should) satisfy the *leftist property*: the rank of any left child is at least as large as
the rank of its right sibling.

Note that this implies that the right-most branch is always the shortest path to `LftHeap.empty`.
-/
inductive LftHeap (α : Type) : Type where
| empty : LftHeap α
| node : Nat → α → LftHeap α → LftHeap α → LftHeap α

namespace LftHeap
  variable {α : Type} [O : Ord α]

  /-- A heap with just one element. -/
  abbrev just (a : α) : LftHeap α :=
    node 1 a empty empty

  /-- Depth of a heap. -/
  def depth : LftHeap α → Nat
  | empty => 0
  | node _ _ lft rgt =>
    1 + max lft.depth rgt.depth

  /-- Extracts the rank of a heap. -/
  def rank : LftHeap α → Nat
  | empty => 0
  | node r .. => r

  /-- Builds a node respecting the *leftist property*, assuming its inputs do respect it. -/
  def mk (e : α) (t₁ t₂ : LftHeap α) : LftHeap α :=
    let (r₁, r₂) := (t₁.rank, t₂.rank)
    if r₂ ≤ r₁
    then node r₂.succ e t₁ t₂
    else node r₁.succ e t₂ t₁

  section merge
    /-- Merges two heaps respecting the *leftist property*. -/
    def merge : LftHeap α → LftHeap α → LftHeap α
    | empty, h | h, empty => h
    | h₁@(node _r₁ e₁ lft₁ rgt₁), h₂@(node _r₂ e₂ lft₂ rgt₂) =>
      match compare e₁ e₂ with
      | .lt | .eq => merge rgt₁ h₂ |> mk e₁ lft₁
      | .gt => merge h₁ rgt₂ |> mk e₂ lft₂

    termination_by
      merge lft rgt => lft.depth + rgt.depth
    -- Ugly proof because I seldom need to do termination proofs, my tactic-fu is too weak to make
    -- this proof as simple as it needs to be. See [fromList] for a better termination proof.
    decreasing_by
      rename h₁ = node _r₁ e₁ lft₁ rgt₁ => h₁_def
      rename h₂ = node _r₂ e₂ lft₂ rgt₂ => h₂_def
      simp_wf
      simp [h₁_def, h₂_def, depth]
      simp_arith
      try apply Nat.le_max_left
      try apply Nat.le_max_right
  end merge

  /-- Inserts a value in the heap. -/
  def insert (a : α) (h : LftHeap α) : LftHeap α :=
    just a |>.merge h

  /-- Top value in the heap. -/
  def min? : LftHeap α → Option α
  | empty => none
  | node _ m _ _ => m

  /-- Removes the top value if any. -/
  def removeMin? : LftHeap α → Option (LftHeap α)
  | empty => none
  | node _ _ lft rgt => lft.merge rgt

  @[inherit_doc removeMin?]
  def removeMin (h : LftHeap α) : LftHeap α :=
    h.removeMin?.getD h

  section fromList
    /-- Turns a list in a heap. -/
    def fromList : List α → LftHeap α :=
      aux [] ∘ List.map just
    where
      aux  : List (LftHeap α) → List (LftHeap α) → LftHeap α
      -- presentation optimized for proofs, *termination* proofs in particular
      | [], [] => empty
      | [h], []
      | [], [h] => h
      | fst::snd::tl, [] => aux [fst.merge snd] tl
      | fst::tl, [h] => aux [fst.merge h] tl
      | acc, fst::snd::tl =>
        let h := fst.merge snd
        aux (h::acc) tl

    termination_by
      aux acc l => acc.length + l.length
    decreasing_by
      simp_wf ; simp_arith
  end fromList
end LftHeap



/-! ## Binomial heaps

A *binomial tree* over elements of type `α` and of rank `r` is a `node` with `r` children `t₁`, ...,
`tᵣ` where each `tᵢ` is a binomial tree of rank `r - i`.

Binomial trees of rank 0, 1, 2, and 3 look as follows.

```
rank 0 | rank 1 | rank 2 | rank 3
  o    |   o    |    o   |      o
       |   |    |   /|   |     /|\
       |   o    |  o o   |    o o o
       |        |  |     |   /| |
       |        |  o     |  o o o
       |        |        |  |
       |        |        |  o
```

Simple, unsafe version:

```lean
inductive Tree (α : Type u) : Type u
/-- `node r e subs` is the node of rank `r` storing element `e` with sub-trees `subs`. -/
| node : Nat → α → List (Tree α) → Tree α
```
-/



mutual
  /-- Dependent binomial tree structure. -/
  inductive BHeap.Tree : Type u → Nat → Type u
  | node : α → TreeList α r → Tree α r

  /-- Dependent `Tree` list structure. -/
  inductive BHeap.TreeList : Type u → Nat → Type u
  | nil : TreeList α 0
  | cons : Tree α r → TreeList α r → TreeList α r.succ
end

namespace BHeap

scoped infixr:67 " ::: " => TreeList.cons

namespace Tree
  variable {α : Type} [Ord α]

  /-- Leaf constructor. -/
  abbrev leaf : α → Tree α 0 :=
    (node · .nil)

  /-- Rank accessor. -/
  def rank : Tree α r → Nat :=
    𝕂 r
  /-- Top element accessor. -/
  def top : Tree α r → α
  | node top _ => top
  /-- Sub-tree accessor. -/
  def kids : Tree α r → TreeList α r
  | node _ kids => kids

  /-- Links two trees of equal rank. -/
  def link : Tree α r → Tree α r → Tree α r.succ
  | t₁@(node top₁ kids₁), t₂@(node top₂ kids₂) =>
    match compare top₁ top₂ with
    | .lt | .eq =>
      node top₁ (t₂ ::: kids₁)
    | .gt =>
      node top₂ (t₁ ::: kids₂)

  protected def compareRank : Tree α r → Tree α r' → Ordering :=
    𝕂 $ 𝕂 $ compare r r'

  def rankLt : Tree α r → Tree α r' → Bool :=
    𝕂 $ 𝕂 $ r < r'
end BHeap.Tree



namespace BHeap.Tree
  abbrev Simple (α : Type u) :=
    (r : Nat) × Tree α r

  instance instCoeSimple : CoeDep (Tree α r) t (Simple α) where
    coe := ⟨r, t⟩

  def toSimple (t : Tree α r) : Simple α :=
    t

  namespace Simple
    def leaf (a : α) : Simple α :=
      Tree.leaf a

    @[simp]
    abbrev rank (s : Simple α) : Nat :=
      s.fst
    @[simp]
    abbrev tree (s : Simple α) : Tree α s.rank :=
      s.snd

    instance instCoeTree : CoeDep (Simple α) s (Tree α s.rank) where
      coe := s.tree

    @[simp]
    abbrev rankLt : Simple α → Simple α → Bool
    | ⟨r, _⟩, ⟨r', _⟩ => r < r'

    abbrev rank_lt (lft rgt : Simple α) : Prop :=
      lft.rankLt rgt

    instance instDecidableRankLt : ∀ (l r : Simple α), Decidable (l.rank_lt r) :=
      fun l r => if h : l.rankLt r then isTrue h else isFalse h
end BHeap.Tree.Simple



open BHeap (Tree)
open List (Chain' Chain)

/-- Binary heap structure.

- does not carry the proof that the list is ordered;
- functions not proved to respect the order.
-/
structure BHeap (α : Type u) where
  trees : List ( Tree.Simple α )

namespace BHeap
  instance instCoeToList : Coe (BHeap α) (List $ Tree.Simple α) where
    coe := trees
  instance instCoeOfList : Coe (List $ Tree.Simple α) (BHeap α) where
    coe := mk

  @[simp]
  abbrev nil : BHeap (α : Type u) :=
    ⟨[]⟩

  def cons : Tree.Simple α → BHeap α → BHeap α
  | s, ⟨l⟩ => ⟨s :: l⟩

  scoped infixr:67 " ::: " => cons

  def length : BHeap α → Nat :=
    List.length ∘ trees

  def insertTree [Ord α] : Tree α r → BHeap α → BHeap α
  | t, ⟨[]⟩ => ⟨[t]⟩
  | t, ⟨ heap@( ⟨r', t'⟩::tl ) ⟩ =>
    if r < r' then
      t.toSimple :: heap
    else if h_eq : r = r' then
      let linked := t.link (h_eq ▸ t')
      insertTree linked tl
    else
      let bh := insertTree t tl
      bh.cons ⟨r', t'⟩

  def insert [Ord α] (a : α) (bh : BHeap α) : BHeap α :=
    Tree.leaf a |> bh.insertTree

  def merge [Ord α] : BHeap α → BHeap α → BHeap α
  | bh, ⟨[]⟩| ⟨[]⟩, bh => bh
  | ⟨trees₁@( ⟨r₁, t₁⟩::tl₁ )⟩, ⟨trees₂@( ⟨r₂, t₂⟩::tl₂ )⟩ =>
    if rank_eq : r₁ = r₂ then
      let linked := t₁.link (rank_eq ▸ t₂)
      let bh := merge tl₁ tl₂
      bh.insertTree linked
    else if r₁ < r₂ then
      merge tl₁ trees₂
      |>.trees.cons ⟨r₁, t₁⟩
    else
      merge trees₁ tl₂
      |>.trees.cons ⟨r₂, t₂⟩
  termination_by merge l r => l.length + r.length
  decreasing_by
    simp_wf
    simp [*, length, Nat.succ_add, Nat.add_succ]
    try (
      apply Nat.lt_trans (Nat.lt_succ_self _)
      exact Nat.lt_succ_self _
    )

  def map (f : Tree.Simple α → β) (bh : BHeap α) : List β :=
    bh.trees.map f

  def ranks : BHeap α → List Nat :=
    map Tree.Simple.rank

  def foldlM
    {α : Type u} {β : Type v}
    {M : Type v → Type w} [Monad M]
    (f : β → Tree.Simple α → M β)
    (init : β)
    (bh : BHeap α)
  : M β :=
    bh.trees.foldlM f init

  def foldrM
    {α : Type u} {β : Type v}
    {M : Type v → Type w} [Monad M]
    (f : Tree.Simple α → β → M β)
    (init : β)
    (bh : BHeap α)
  : M β :=
    bh.trees.foldrM f init

  /-- Big-endian binary representation. -/
  def toBin : BHeap α → List Bool
  | ⟨l⟩ => aux [] 0 l
  where
    aux acc rankExp : List (Tree.Simple α) → List Bool
      | [] => acc
      | hd::tl =>
        let acc := complete acc (hd.rank - rankExp)
        aux (true::acc) hd.rank.succ tl
    complete (l : List Bool) : Nat → List Bool
      | 0 => l
      | n + 1 => complete (false::l) n

  /-- Big-endian binary string using `0`-s and `1`-s. -/
  def toBinString (bh : BHeap α) (minLength : Nat := 0) : String :=
    let bin := bh.toBin
    let bin := if bin.isEmpty then [false] else bin
    let offset := minLength - bin.length
    bin.foldr
      (fun b s => (if b then "1" else "0") ++ s)
      ""
    |> offset.repeat ("0" ++ ·)


  scoped instance instOrdUnit : Ord Unit where
    compare _ _ := .eq

  /-- Binary represention for naturals as ranks of the trees in a `BHeap`.

  The concrete "element" type in the `BHeap` does not matter as we're only interested in the ranks
  of the trees appearing in the `BHeap`. We use `Unit`, which is why we added a `Ord Unit` instance
  to access `BHeap`'s `insert`/`merge` functions.
  -/
  abbrev BNat :=
    BHeap Unit

  namespace BNat
    export BHeap (toBin toBinString)

    def zero : BNat :=
      ⟨[]⟩
    def isZero : BNat → Bool
    | ⟨[]⟩ => true
    | _ => false

    def succ : BNat → BNat :=
      insert default

    def ofNat : Nat → BNat
    | 0 => zero
    | n + 1 => ofNat n |> succ

    instance instOfNat : OfNat BNat n where
      ofNat := ofNat n

    def add (c c' : BNat) : BNat :=
      c.merge c'

    instance instAdd : Add BNat :=
      ⟨add⟩

    def toNat (cnt : BNat) : Nat :=
      cnt.ranks.foldl (fun n r => n + 2^r) 0

    def mul : BNat → BNat → BNat
    | ⟨[]⟩, _ | _, ⟨[]⟩ => zero
    | lft, rgt => aux lft zero rgt.toNat
    where
      aux lft acc : Nat → BNat
      | 0 => acc
      | n + 1 => aux lft (lft + acc) n

    instance instMul : Mul BNat :=
      ⟨mul⟩
  end BNat


  namespace Test
    def display (bh : BHeap α) (blah : Option String) (withInfo : Bool) : IO Unit := do
      if let some blah := blah then
        println! blah
      if withInfo then
        println! "{bh.ranks}"
        println! "- bin list: {bh.toBin}"
        println! "- bin: {bh.toBinString 8}"
      else
        println! "{bh.toBinString 8}"

    def test_insert₁ (withInfo := false) : IO Unit := do
      let mut bh : BHeap Nat := nil
      display bh none withInfo
      bh := bh.insert 0
      display bh none withInfo
      bh := bh.insert 0
      display bh none withInfo
      bh := bh.insert 0
      display bh none withInfo
      bh := bh.insert 0
      display bh none withInfo
      bh := bh.insert 0
      display bh none withInfo
      bh := bh.insert 0
      display bh none withInfo
      bh := bh.insert 0
      display bh none withInfo

    #eval test_insert₁

    def test_count (withInfo := false) : IO Unit := do
      let mut cnt : BNat := 0
      display cnt s!"cnt := 0 | {cnt.toNat}" withInfo
      cnt := 6
      display cnt s!"cnt := 6 | {cnt.toNat}" withInfo
      cnt := 11
      display cnt s!"cnt := 11 | {cnt.toNat}" withInfo

      cnt := cnt + 7
      display cnt s!"cnt := cnt + 7 | {cnt.toNat}" withInfo
      cnt := cnt + 0
      display cnt s!"cnt := cnt + 0 | {cnt.toNat}" withInfo

      cnt := cnt * 10
      display cnt s!"cnt := cnt * 10 | {cnt.toNat}" withInfo

      cnt := cnt * 0
      display cnt s!"cnt := cnt * 0 | {cnt.toNat}" withInfo

    #eval test_count
  end Test

end BHeap
