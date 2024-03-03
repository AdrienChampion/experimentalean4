import Pfds.Init



/-! # Dependent lists

This file contains two encoding for dependent lists. `AsStructure.DList` is based on lean's builtin
`List`-s, while `AsInductive.DList` is a self-contained `inductive` definition.
-/
namespace DList



/-! ## Dependent lists as a structure

This encoding packs a lean builtin lists and a proof regarding its length.
-/
namespace AsStructure


/-- Dependent list structure.

### Coercions

We can't write the `Coe (DList len α) (List α)` instance because of a semi-out-param problem
on the `len` type parameter. So conversion has to go through `DList.ofList` or `List.toDList`.

We do have (dependent) coercion from `List α` however. -/
structure DList (len : Nat) (α : Type u) : Type u where mkRaw ::
  /-- Conversion to `List`. -/
  toList : List α
  /-- Length invariant. -/
  h_len : toList.length = len

namespace DList
  variable {α : Type u}

  /-- Yields the length of the dependent list. -/
  def length : DList l α → Nat :=
    𝕂 l

  /-- Turns a `List` in a `DList`. -/
  abbrev ofList (l : List α) : DList l.length α :=
    ⟨l, rfl⟩

  instance instCoeOfList : CoeDep (List α) list (DList list.length α) :=
    ⟨ofList list⟩

  /-- Same as `h_len`, only here to make it `@[simp]`. -/
  @[simp]
  theorem len_invariant (dl : DList len α) : dl.toList.length = len :=
    dl.h_len

  /-- Empty d-list. -/
  abbrev nil : DList 0 α :=
    ⟨[], rfl⟩

  /-- D-list with a single element. -/
  abbrev one : α → DList 1 α :=
    fun a => ⟨[a], rfl⟩

  @[inherit_doc one]
  abbrev singleton : α → DList 1 α :=
    one

  /-- Adds an element at the head of the d-list. -/
  @[simp]
  def cons (hd : α) (tl : DList len α) : DList len.succ α where
    toList := hd :: tl.toList
    h_len := by
      simp [List.length, tl.h_len]

  scoped infixr:67 " ::: " => cons

  /-- Generates a d-list repeating an element `n` times. -/
  def gen : (n : Nat) → α → DList n α
  | 0, _ => nil
  | n + 1, e => e ::: gen n e

  instance instInhabited [Inhabited α] : Inhabited (DList len α) :=
    ⟨gen len default⟩

  /-- Reverses a d-list. -/
  def rev (dl : DList len α) : DList len α :=
    ⟨dl.toList.reverse, by simp⟩

  /-- D-list concatenation. -/
  def concat (dl₁ : DList len₁ α) (dl₂ : DList len₂ α) : DList (len₁ + len₂) α :=
    ⟨dl₁.toList ++ dl₂.toList, by simp⟩

  section monadic
    variable
      {M : Type u → Type v} [Monad M]

    /-- Monadic map (left-to-right). -/
    def mapM (f : α → M β) : DList len α → M (DList len β)
    | ⟨[], h_len⟩ => do
      return h_len ▸ nil
    | ⟨hd::tl, h_len⟩ => do
      let hd ← f hd
      let tl ← ofList tl |>.mapM f
      return h_len ▸ (hd ::: tl)

    /-- Left-to-right monadic fold. -/
    def foldlM (f : β → α → M β) (init : β) : DList len α → M β :=
      List.foldlM f init ∘ toList
    /-- Right-to-left monadic fold. -/
    def foldrM (f : α → β → M β) (init : β) : DList len α → M β :=
      List.foldrM f init ∘ toList

    /-- Monadic fold, `fromRight` forces right-to-left traversal (default false). -/
    def foldM
      (f : β → α → M β) (init : β)
      (dl : DList len α)
      (fromRight := false)
    : M β :=
      if fromRight
      then dl.foldlM f init
      else dl.foldrM (fun a b => f b a) init

    /-- Monadic boolean *forall* over d-lists. -/
    def allM {M : Type → Type u} [Monad M]
      (f : α → M Bool) (dl : DList len α)
    : M Bool :=
      dl.toList.allM f

    /-- Monadic boolean *exists* over d-lists. -/
    def anyM {M : Type → Type u} [Monad M]
      (f : α → M Bool) (dl : DList len α)
    : M Bool :=
      dl.toList.anyM f
  end monadic

  /-- Maps a d-list. -/
  def map : (α → β) → DList len α → DList len β :=
    mapM (M := Id)

  /-- Left-to-right fold. -/
  def foldl : (β → α → β) → β → DList len α → β :=
    foldlM (M := Id)
  /-- Right-to-left fold. -/
  def foldr : (α → β → β) → β → DList len α → β :=
    foldrM (M := Id)

  /-- D-list fold, `fromRight` forces right-to-left traversal (default false). -/
  def fold
    (f : β → α → β) (init : β)
    (dl : DList len α)
    (fromRight : Bool := false)
  : β :=
    if fromRight
    then dl.foldl f init
    else dl.foldr (fun a b => f b a) init

  /-- *Forall* over d-lists. -/
  def all (f : α → Bool) (dl : DList len α) : Bool :=
    dl.toList.all f

  /-- *Exists* over d-lists. -/
  def any (f : α → Bool) (dl : DList len α) : Bool :=
    dl.toList.any f



  instance instPure : Pure (DList len) where
    pure := gen len

  instance instFunctor : Functor (DList len) where
    map := map

  instance instForIn {M : Type u → Type v} : ForIn M (DList len α) α where
    forIn dl := forIn dl.toList



  section getters_setters
    variable (dl : DList len α)

    /-- Legal element getter. -/
    def get : Fin len → α :=
      dl.h_len ▸ dl.toList.get

    /-- Gives access to `dl[idx]` notation for `get`. -/
    instance instGetElem : GetElem (DList len α) Nat α fun _ i => i < len where
      getElem dl i h := dl.get ⟨i, h⟩

    /-- Legal setter. -/
    def set : Fin len → α → DList len α
    | ⟨idx, _⟩, val =>
      let lst := (dl.h_len ▸ dl.toList.set) idx val
      ⟨lst, by simp⟩

    variable (idx : Nat)

    /-- Retrieves a value if the index is legal. -/
    def get? : Option α :=
      if h : idx < len
      then dl[idx]
      else none

    /-- The element at `idx` if legal, `default` otherwise. -/
    def getD (default : α) : α :=
      dl.get? idx |>.getD default

    @[inherit_doc getD]
    def getI [Inhabited α] : α :=
      dl.get? idx |>.getD default

    /-- Panics on illegal indices. -/
    def get! [Inhabited α] : α :=
      if h : idx < len
      then dl[idx]
      else panic! s!"`DList.get!` called on list of length `{len}` with illegal index `{idx}`"

    /-- Sets an element if `idx` is legal, `none` otherwise. -/
    def set? (val : α) : Option (DList len α) :=
      if h : idx < len
      then dl.set ⟨idx, h⟩ val
      else none

    /-- Sets a value if `idx` is legal, identity otherwise. -/
    def set! (val : α) : DList len α :=
      dl.set? idx val |>.getD dl
  end getters_setters



  /-! ## Some proofs, why not -/

  @[simp]
  theorem map_list_cons :
    ∀ {a : α} {as : List α} {f : α → β},
      map f ⟨a::as, rfl⟩ = f a ::: map f ⟨as, rfl⟩
  := by
    simp [map, mapM]

  @[simp]
  theorem map_cons :
    ∀ {a : α} {as : DList len α} {f : α → β},
      map f (a:::as) = f a ::: as.map f
  := fun {_} => by
    intro | mkRaw _ h => cases h ; simp

  @[simp]
  theorem len_0_eq_nil : ∀ {as : DList 0 α}, as.toList = []
  | ⟨[], _⟩ => rfl

  @[simp]
  theorem len_1_eq_singleton : ∀ {as : DList 1 α}, ∃ (a : α), as = ⟨[a], rfl⟩
  | ⟨[a], _⟩ => ⟨a, rfl⟩

  theorem len_0 {P : Prop} : ∀ (as : DList 0 α), (as.toList = [] → P) → P := by
    simp
end AsStructure.DList



namespace AsInductive

inductive DList : Type u → Nat → Type u
| nil : DList α 0
| cons : α → DList α len → DList α len.succ

namespace DList
  scoped infixr:67 " ::: " => cons

  variable {α : Type u}
    -- {len : Nat} -- we don't want `len` as a variable here

  @[simp]
  abbrev length : DList α len → Nat :=
    𝕂 len

  abbrev ofList : (l : List α) → DList α l.length
  | [] => DList.nil
  | hd::tl => hd ::: ofList tl

  instance instCoeOfList : CoeDep (List α) l (DList α l.length) :=
    ⟨ofList l⟩

  def gen : (n : Nat) → α → DList α n
  | 0, _ => nil
  | n + 1, e => e ::: gen n e

  instance instInhabited [Inhabited α] : Inhabited (DList α len) :=
    ⟨gen len default⟩

  def rev (dl : DList α len) : DList α len :=
    aux nil dl len.zero_add
  where
    aux {lenAcc lenRest : Nat}
      (acc : DList α lenAcc)
      (rest : DList α lenRest)
      (h : lenAcc + lenRest = len)
    : DList α len :=
      match rest with
      | nil => h ▸ acc
      | hd ::: tl =>
        aux (hd ::: acc) tl
        $ by simp [h, Nat.succ_add_eq_add_succ]

  def revAppendTo {len len' : Nat} : DList α len → DList α len' → DList α (len + len')
  | nil, dl' => by simp ; exact dl'
  | dl, nil => by simp ; exact dl.rev
  | hd:::dl, dl' => by
    rw [Nat.succ_add_eq_add_succ]
    exact dl.revAppendTo (hd:::dl')

  def concat (dl : DList α len) : DList α len' → DList α (len + len') :=
    dl.rev.revAppendTo



  section monadic
    variable
      {α : Type}
      {β : Type v}
      {M : Type v → Type w} [Monad M]

    def mapM {len : Nat} (f : α → M β) : DList α len → M (DList β len)
    | nil => pure nil
    | hd:::tl => do
      let hd ← f hd
      let tl ← tl.mapM f
      return hd:::tl

    def foldlM {len : Nat} (f : β → α → M β) (init : β) : DList α len → M β
    | nil => pure init
    | hd:::tl => do
      let acc ← f init hd
      tl.foldlM f acc

    def foldrM {len : Nat} (f : α → β → M β) (init : β) : DList α len → M β
    | nil => pure init
    | hd:::tl => do
      let acc ← tl.foldrM f init
      f hd acc

    def allM {M : Type → Type u} [Monad M] {len : Nat}
      (f : α → M Bool)
      (early := true)
    : DList α len → M Bool
    | nil => pure true
    | hd:::tl => do
      let okay ← f hd
      if early ∧ ¬ okay then
        return false
      else
        tl.allM f early

    #guard ofList [1, 2, 3, 4] |>.allM (M := Id) (· ≠ 0 |> pure)

    def anyM {M : Type → Type u} [Monad M]
      (f : α → M Bool)
      (early := true)
      (dl : DList α len)
    : M Bool :=
      not <$> dl.allM (fun a => not <$> f a) early

    #guard ofList [1, 2, 3, 4] |>.anyM (M := Id) (· ≠ 0 |> pure)
  end monadic
end AsInductive.DList
