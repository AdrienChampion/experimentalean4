--! Messing around with Rust-flavored iterators.



--- Instantiated by iterators.
class Iter (I : Type u) where
  --- Type of the items we're iterating on.
  Item : Type i
  --- If there is a next element, produces it and the updated iterator.
  next : I → Option (Item × I)

--- Can be turned into an iterator.
class IntoIter (Src : Type v) where
  --- Target iterator type.
  IntoIter : Type i
  --- [`Iter`] instance.
  IntoIterIsIter : Iter IntoIter
  --- Produces the iterator.
  intoIter : Src → IntoIter

--- Can be created from an iterator.
class FromIter (Tgt : Type u → Type v) where
  --- Produces the target type.
  fromIter [Iter I] : I → Tgt (Iter.Item I)



section listIter
  partial def List.fromIter
    [Iter I] (iter : I)
    : List (Iter.Item I)
  :=
    match Iter.next iter with
    | none => []
    | some (elm, iter) => elm::(fromIter iter)

  instance ListFromIter : FromIter List where
    fromIter := List.fromIter

  structure List.Iterator (α : Type u) where
    list : List α
  deriving Repr

  instance ListIteratorIsIter : Iter (List.Iterator α) where
    Item := α
    next self :=
      match self.list with
      | [] => none
      | next::tail => some (next, List.Iterator.mk tail)

  def List.intoIter (self : List α) : Iterator α :=
    Iterator.mk self

  instance ListIntoIter : IntoIter (List α) where
    IntoIter := List.Iterator α
    IntoIterIsIter := inferInstance
    intoIter self := self.intoIter
end listIter



section arrayIter
  --- An array is just a list, let's re-use `List.fromIter`.
  partial def Array.fromIter
    [Iter I] (iter : I)
    : Array (Iter.Item I)
  :=
    List.fromIter iter |> Array.mk

  instance ArrayFromIter : FromIter Array where
    fromIter := Array.fromIter

  --- Again, an array is actually just a `data` field of type `List α`, so we could just user
  --- `List.Iterator`. This version is actually much worse performance-wise, because of all the
  --- `Array.get`s. But then again maybe something super clever happens during codegen.
  structure Array.Iterator (α : Type u) where
    array : Array α
    cursor : Nat
  deriving Repr

  def Array.Iterator.new (array : Array α) : Iterator α :=
    Iterator.mk array 0

  instance Array.IteratorIsIter : Iter (Iterator α) where
    Item := α
    next self :=
      if legal : self.cursor < self.array.size then
        let elm :=
          Fin.mk self.cursor legal
          |> self.array.get
        some (elm, Array.Iterator.mk self.array (self.cursor + 1))
      else
        none

  def Array.intoIter (self : Array α) : Iterator α :=
    Iterator.new self

  instance ArrayIntoIter : IntoIter (Array α) where
    IntoIter := Array.Iterator α
    IntoIterIsIter := inferInstance
    intoIter self := self.intoIter
end arrayIter



section combineIter
  structure Iter.FilterMap
    (I : Type u)
    [Iter I]
    (Out : outParam (Type v))
  where
    filterMap : Iter.Item I → Option Out
    subIter : I

  def Iter.filterMap
    [Iter I]
    (subIter : I) (filterMap : Iter.Item I → Option Out)
    : FilterMap I Out
  :=
    { filterMap, subIter }

  private partial def Iter.FilterMap.innerNext
    [Iter I]
    (self : Iter.FilterMap I Out)
    (iter : I)
    : Option (Out × Iter.FilterMap I Out)
  :=
    match Iter.next iter with
    | none => none
    | some (elm, iter) =>
      match self.filterMap elm with
      | none => self.innerNext iter
      | some out => some (out, FilterMap.mk self.filterMap iter)

  instance FilterMapIter [Iter I] : Iter (Iter.FilterMap I Out) where
    Item := Out
    next self := self.innerNext self.subIter


  structure Iter.Zip
    (I₁ I₂ : Type u)
    [Iter I₁]
    [Iter I₂]
  where
    subIter₁ : I₁
    subIter₂ : I₂
  
  def Iter.zip
    [Iter I₁]
    [Iter I₂]
    : I₁ → I₂ → Zip I₁ I₂
  := Iter.Zip.mk

  instance ZipIter [Iter I₁] [Iter I₂] : Iter (Iter.Zip I₁ I₂) where
    Item := Iter.Item I₁ × Iter.Item I₂
    next self :=
      match (Iter.next self.subIter₁, Iter.next self.subIter₂) with
      | (none, _) | (_, none) => none
      | (some (n₁, i₁), some (n₂, i₂)) => some ((n₁, n₂), Iter.zip i₁ i₂)
end combineIter



section dumbExamples

  def List.filterEvenToArrayString
    (self : List Nat)
    : Array String
  :=
    Iter.filterMap self.intoIter (
      fun (n : Nat) =>
        if n % 2 = 0 then toString n |> some else none
    )
    |> Array.fromIter

  def List.filterOddToArrayString
    (self : List Nat)
    : Array String
  :=
    Iter.filterMap self.intoIter (
      fun (n : Nat) =>
        if n % 2 = 1 then toString n |> some else none
    )
    |> Array.fromIter
  
  def list : List Nat := [0, 1, 2, 3, 4, 5, 6]

  #eval list.filterEvenToArrayString
  #eval list.filterOddToArrayString

  def merged : List (String × String) :=
    let even :=
      list.filterEvenToArrayString
      |> Array.intoIter
    let odd :=
      list.filterOddToArrayString
      |> Array.intoIter
    Iter.zip even odd
    |> List.fromIter
  #eval merged

end dumbExamples