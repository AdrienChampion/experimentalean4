import Pfds.Init



/-! # Chapter 2 -/
namespace Pfds.C2



/-- Binary tree, leaf carry no (`α`) data.

This is not checked, but values of this type are expected to respect the invariant

- `node lft e rgt`: `∀ (l ∈ lft), l ≤ e` and `∀ (r ∈ rgt), e ≤ r`.

This is (hopefully) guaranteed as long as you don't construct invalid values using the `node`
constructor.

On invalid trees, functions like `mem`, `add?`, `get?`, and `set?` return arbitrary outputs.
-/
inductive Tree (α : Type) : Type
| empty : Tree α
| node : Tree α → α → Tree α → Tree α
deriving DecidableEq, Inhabited

namespace Tree
  variable
    {α : Type}
    [O : Ord α]

  /-- The tree with a single node. -/
  @[simp]
  abbrev just : α → Tree α :=
    (node empty · empty)

  /-- Maximal branch depth. -/
  def depth : Tree α → Nat
  | empty => 0
  | node l _ r =>
    (max l.depth r.depth) + 1

  /-- List of all branch depths. -/
  def depths : Tree α → List Nat
  | empty => [0]
  | node l _ r =>
    l.depths ++ r.depths
    |>.map .succ

  /-- Number of elements in the tree. -/
  def size : Tree α → Nat
  | empty => 0
  | node l _ r =>
    l.size + r.size + 1

  /-- Element in the top node, if any. -/
  def top? : Tree α → Option α
  | empty => none
  | node _ top _ => top

  /-- True the value is (`Ord`-)equal to a value in the tree. -/
  def mem : α → Tree α → Bool
  | _, empty => false
  | a, node lft e rgt =>
    match compare a e with
    | .lt => lft.mem a
    | .eq => true
    | .gt => rgt.mem a

  instance instMembership : Membership α (Tree α) where
    mem a t := t.mem a

  instance instDecidableMembership (a : α) (t : Tree α) : Decidable (a ∈ t) :=
    if h : t.mem a
    then isTrue h
    else isFalse h

  /-- Inserts a value in a tree, if needed. See also `add`. -/
  def add? : α → Tree α → Option (Tree α)
  | a, empty =>
    node empty a empty
  | a, node lft e rgt =>
    match compare a e with
    | .eq => none
    | .lt =>
      lft.add? a >>= (node · e rgt)
    | .gt =>
      rgt.add? a >>= (node lft e ·)

  /-- Inserts a value in a tree, see also `add?`. -/
  def add (a : α) (t : Tree α) : Tree α :=
    t.add? a |>.getD t

  /-- Value associated to a key in an associative tree. -/
  def get? : α → Tree (α × β) → Option β
  | _, empty => none
  | a, node lft (key, val) rgt =>
    match compare a key with
    | .eq => val
    | .lt => lft.get? a
    | .gt => rgt.get? a

  /-- Sets the value associated to a key in an associative tree. -/
  def set? : α → β → Tree (α × β) → Option β × Tree (α × β)
  | k, v, empty => (none, just (k, v))
  | k, v, node lft (key, val) rgt =>
    match compare k key with
    | .eq => (val, node lft (k, v) rgt)
    | .lt =>
      let (prev?, lft) := lft.set? k v
      (prev?, node lft (key, val) rgt)
    | .gt =>
      let (prev?, rgt) := rgt.set? k v
      (prev?, node lft (key, val) rgt)

  /-- Generates a tree in which all branches have the same depth, and all nodes have the same
  element.
  -/
  def complete (a : α) : Nat → Tree α
  | 0 => empty
  | n + 1 =>
    let sub := complete a n
    node sub a sub

  /-- Generates a *balanced* tree with a certain sized, where all nodes have the same element.

  A tree is *balanced* if none of its branches have depths that differ by more than `1`.
  -/
  partial def balanced (a : α) : Nat → Tree α
  | 0 => empty
  | 1 => just a
  | n + 1 =>
    let (lft, rgt) :=
      let nLft := n / 2
      if nLft * 2 = n then
        let sub := balanced a nLft
        (sub, sub)
      else
        (balanced a nLft, balanced a (n - nLft))
    node lft a rgt

  -- #eval do
  --   let size := 4
  --   let t := balanced "cat" size
  --   if t.size ≠ size then
  --     IO.throwServerError s!"size: {t.size}, expected {size}"
  --   println! "depths: {t.depths.dedup}"
end Tree



section set_and_map

  /-- Basic set spec. -/
  class Set (α : Type) (S : Type) where
    empty : S
    mem : α → S → Bool
    add? : α → S → Option S

  instance Tree.instSet [Ord α] : Set α (Tree α) where
    empty := Tree.empty
    mem := Tree.mem
    add? := Tree.add?

  /-- Basic map spec. -/
  class Map (α β : Type) (M : Type) where
    empty : M
    get? : α → M → Option β
    set? : α → β → M → Option β × M

  instance Tree.instmap [Ord α] : Map α β (Tree (α × β)) where
    empty := Tree.empty
    get? := Tree.get?
    set? := Tree.set?

end set_and_map



/-! ## A bunch of stuff that has nothing to do with the book but why not -/
namespace Tree

  instance instPure : Pure Tree where
    pure := just

  /-- Monadic map.

  - `(rev := true)` for right-to-left traversal (default `false`).
  -/
  def mapM [Monad M] : (α → M β) → Tree α → (rev : Bool := false) → M (Tree β)
  | _, empty, _ => pure empty
  | f?, node lft e rgt, rev =>
    if ¬ rev then do
      let lft ← lft.mapM f? rev
      let e ← f? e
      let rgt ← rgt.mapM f? rev
      return node lft e rgt
    else do
      let rgt ← rgt.mapM f? rev
      let e ← f? e
      let lft ← lft.mapM f? rev
      return node lft e rgt

  /-- Maps a function over the elements of a tree. -/
  protected def map : (α → β) → Tree α → Tree β :=
    mapM (M := Id)

  instance instFunctor : Functor Tree where
    map := Tree.map

  /-- Monadic fold.

  - `(rev := true)` for right-to-left traversal (default `false`).
  -/
  def foldM [Monad M] : (β → α → M β) → β → Tree α → (rev : Bool := false) → M β
  | _, acc, empty, _ => pure acc
  | f?, acc, node lft e rgt, rev => do
    let acc ← if ¬ rev
      then lft.foldM f? acc rev
      else rgt.foldM f? acc rev
    let acc ← f? acc e
    if ¬ rev
    then rgt.foldM f? acc rev
    else lft.foldM f? acc rev

  /-- Folds over the elements of a tree.

  - `(rev := true)` for right-to-left traversal (default `false`).
  -/
  def fold (f : β → α → β) (init : β) (t : Tree α) (rev : Bool := false) : β :=
    t.foldM (M := Id) f init rev

  def find (okay : α → Bool) : (t : Tree α) → Option α
  | empty => none
  | node lft e rgt =>
    if okay e then
      e
    else if let some a := lft.find okay then
      a
    else if let some a := rgt.find okay then
      a
    else
      none
end Tree



/-! ## Trying to prove, probably going to go very bad -/
namespace Tree
  inductive Mem : α → Tree α → Prop
  | top : ∀ {a : α} {lft rgt : Tree α},
    Mem a (node lft a rgt)
  | lft : ∀ {a e : α} {lft rgt : Tree α},
    lft.Mem a → Mem a (node lft e rgt)
  | rgt : ∀ {a e : α} {lft rgt : Tree α},
    rgt.Mem a → Mem a (node lft e rgt)

  instance instMembership' : Membership α (Tree α) where
    mem := Mem

  @[simp]
  theorem mem_empty : ∀ {a : α}, ¬ a ∈ empty := by
    intro _ absurd
    cases absurd

  @[simp]
  theorem find_empty : ∀ {okay : α → Bool}, empty.find okay = none := by
    simp [find]

  theorem find_some
    {okay : α → Bool} {a : α}
  : {t : Tree α} →
    t.find okay = some a → a ∈ t ∧ okay a
  | empty => by simp
  | node lft e rgt => by
    simp [find]
    split ; simp
    · intro eq ; cases eq
      exact ⟨.top, by assumption⟩
    cases h_lft : lft.find okay <;> simp
    · cases h_rgt : rgt.find okay <;> simp
      let _ih := rgt.find_some h_rgt
      intro eq ; cases eq
      exact ⟨.rgt _ih.left, _ih.right⟩
    · let _ih := lft.find_some h_lft
      intro eq ; cases eq
      exact ⟨.lft _ih.left, _ih.right⟩

  theorem find_none
    {okay : α → Bool}
  : {t : Tree α} → (
    t.find okay = none ↔ ∀ (a : α), a ∈ t → ¬ okay a
  )
  | empty => by simp
  | node lft e rgt => by
    unfold find
    split
    · simp
      exact ⟨e, .top, by assumption⟩
    case inr h_e =>
      cases h_lft : find okay lft <;> simp
      · cases h_rgt : find okay rgt <;> simp
        · intro a ; intro
          | .top => simp [h_e]
          | .lft a_in_lft =>
            simp [find_none.mp h_lft a a_in_lft]
          | .rgt a_in_rgt =>
            simp [find_none.mp h_rgt a a_in_rgt]
        case some a =>
          let ih := find_some h_rgt
          exact ⟨a, .rgt ih.left, ih.right⟩
      case some a =>
        let ih := find_some h_lft
        exact ⟨a, .lft ih.left, ih.right⟩

  inductive Valid [LE α] : Tree α → Prop
  | empty : empty.Valid
  | node : ∀ {e : α} {lft rgt : Tree α},
    lft.Valid → rgt.Valid →
    (∀ (l : α), l ∈ lft → l ≤ e) →
    (∀ (r : α), r ∈ rgt → e ≤ r) →
    (node lft e rgt).Valid

  instance instDecidableValid
    [L : LE α]
    [DecidableRel L.le]
  : (t : Tree α) → Decidable t.Valid
  | empty => isTrue .empty
  | node lft e rgt => by
    cases lft.instDecidableValid
    <;> cases rgt.instDecidableValid
    <;> try (
      apply isFalse
      intro h
      cases h
      contradiction
    )
    case isTrue lft_Valid rgt_Valid =>
      cases h_lft : lft.find (¬ · ≤ e)
      case none =>
        cases h_rgt : rgt.find (¬ e ≤ ·)
        case none =>
          apply isTrue ; apply Valid.node lft_Valid rgt_Valid
          · intro l l_in_lft
            let ih := find_none.mp h_lft l l_in_lft
            simp [Decidable.not_not] at ih
            exact ih
          · intro r r_in_rgt
            let ih := find_none.mp h_rgt r r_in_rgt
            simp [Decidable.not_not] at ih
            exact ih
        case some a =>
          apply isFalse ; intro h ; cases h
          case node _ _ _ ih_rgt =>
            let ⟨a_in_rgt, not_e_le_a⟩ := find_some h_rgt
            let absurd := ih_rgt a a_in_rgt
            simp at not_e_le_a
            exact not_e_le_a absurd
      case some a =>
        apply isFalse ; intro h ; cases h
        case node _ ih_lft _ _ =>
          let ⟨a_in_lft, not_a_le_e⟩ := find_some h_lft
          let absurd := ih_lft a a_in_lft
          simp at not_a_le_e
          exact not_a_le_e absurd

  inductive SetLike [Ord α] : Tree α → Prop
  | empty : empty.SetLike
  | node : ∀ {e : α} {lft rgt : Tree α},
    lft.SetLike → rgt.SetLike →
    (∀ (l : α), l ∈ lft → compare l e = .lt) →
    (∀ (r : α), r ∈ rgt → compare r e = .gt) →
    (node lft e rgt).SetLike
end Tree
