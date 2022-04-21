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



partial def Iter.fold
  [Iter I]
  (iter : I)
  (init : Out)
  (step : Out → Iter.Item I → Out)
  : Out
:=
  match next iter with
  | none =>
    init
  | some (elm, iter) =>
    fold iter (step init elm) step

def Iter.collect
  [Iter I]
  [FromIter Tgt]
  (iter : I)
  : Tgt (Iter.Item I)
:=
  FromIter.fromIter iter



section listIter
  partial def List.collect
    [Iter I] (iter : I)
    : List (Iter.Item I)
  :=
    match Iter.next iter with
    | none => []
    | some (elm, iter) => elm::(collect iter)

  instance ListFromIter : FromIter List where
    fromIter := List.collect

  structure List.Iterator (α : Type u) where
    list : List α
  deriving Repr

  instance ListIteratorIsIter : Iter (List.Iterator α) where
    Item := α
    next self :=
      match self.list with
      | [] => none
      | next::tail => some (next, List.Iterator.mk tail)

  def List.iter (self : List α) : Iterator α :=
    Iterator.mk self

  instance ListIntoIter : IntoIter (List α) where
    IntoIter := List.Iterator α
    IntoIterIsIter := inferInstance
    intoIter self := self.iter
end listIter



section arrayIter
  --- An array is just a list, let's re-use `List.collect`.
  partial def Array.collect
    [Iter I] (iter : I)
    : Array (Iter.Item I)
  :=
    List.collect iter |> Array.mk

  instance ArrayFromIter : FromIter Array where
    fromIter := Array.collect

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

  def Array.iter (self : Array α) : Iterator α :=
    Iterator.new self

  instance ArrayIntoIter : IntoIter (Array α) where
    IntoIter := Array.Iterator α
    IntoIterIsIter := inferInstance
    intoIter self := self.iter
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
  
  def Iter.filter
    [Iter I]
    (subIter : I) (filter : Iter.Item I → Bool)
    : FilterMap I (Iter.Item I)
  :=
    let filterMap item :=
      if filter item
      then some item
      else none
    { filterMap, subIter }
  
  def Iter.map
    [Iter I]
    (subIter : I) (map : Iter.Item I → Out)
    : FilterMap I Out
  :=
    let filterMap item :=
      map item |> some
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

  --- Removes the odd naturals in a list.
  def List.filterEvenToArrayString
    (self : List Nat)
    : Array String
  :=
    Iter.filterMap self.iter (
      fun (n : Nat) =>
        if n % 2 = 0 then toString n |> some else none
    )
    |> Iter.collect

  --- Removes the even naturals in a list.
  def List.filterOddToArrayString
    (self : List Nat)
    : Array String
  :=
    Iter.filterMap self.iter (
      fun (n : Nat) =>
        if n % 2 = 1 then toString n |> some else none
    )
    |> Iter.collect

  def list : List Nat := [0, 1, 2, 3, 4, 5, 6]

  #eval list.filterEvenToArrayString
  #eval list.filterOddToArrayString

  def merged : List (String × String) :=
    let even :=
      list.filterEvenToArrayString
      |> Array.iter
    let odd :=
      list.filterOddToArrayString
      |> Array.iter
    Iter.zip even odd
    |> Iter.collect
  #eval merged

  def joined : List String :=
    Iter.map
      merged.iter
      (fun (lft, rgt) => s! "{lft} × {rgt}")
    |> List.collect
  #eval joined

  def folded : String :=
    Iter.fold joined.iter "" (
      fun s (elm : String) =>
        let sep :=
          if s.length = 0
          then ""
          else ", "
        s! "{s}{sep}{elm}"
    )
  #eval folded

end dumbExamples