--! Stream stuff.

import Init.Data.Stream

structure Stream.Unit
instance streamZero (Item : Type u) : Stream Stream.Unit Item where
  next? _ := none

structure Stream.Const (item : Item)
instance streamConst
  {Item : Type u}
  (item : Item)
  : Stream (Stream.Const item) Item
where
  next? self := some (item, self)


section fromStream
  --- Categorical dual of `ToStream`, I'm pretty sure.
  class FromStream
    (collection : Type u)
    (stream : outParam (Type u))
    : Type u
  where
    fromStream : stream → collection

  partial def List.collect
    [Stream S α]
    (stream : S)
    : List α
  :=
    match Stream.next? stream with
    | none => []
    | some (next, stream) => next :: (collect stream)
  instance (α : Type u) [Stream S α] : FromStream (List α) S where
    fromStream := List.collect
  
  partial def Array.collect
    [Stream S α]
    (stream : S)
    : Array α
  :=
    List.collect stream
    |> Array.mk
  instance (α : Type) [Stream S α] : FromStream (Array α) S where
    fromStream := Array.collect
  
  partial def String.collect
    [Stream S Char]
    (stream : S)
    : String
  :=
    List.collect stream
    |> String.mk
  instance [Stream S Char] : FromStream String S where
    fromStream := String.collect
end fromStream



partial def Stream.fold
  [Self : Stream S Item]
  (stream : S)
  (init : Out)
  (step : Out → Item → Out)
  : Out
:=
  match Self.next? stream with
  | none => init
  | some (next, stream) =>
    fold stream (step init next) step



section filter
  structure Stream.Filter
    (S : Type u)
    [Stream S α]
  where
    filter : α → Bool
    subStream : S

  partial def Stream.Filter.next?
    [Stream S α]
    (self : Stream.Filter S)
    : Option (α × Stream.Filter S)
  :=
    match Stream.next? self.subStream with
    | none => none
    | some (next, subStream) =>
      let self := { self with subStream }
      if self.filter next
      then some (next, self)
      else self.next?
  
  instance streamFilter [Stream S α] : Stream (Stream.Filter S) α where
    next? self := self.next?

  def Stream.filter
    [Stream S α]
    (subStream : S) (filter: α → Bool)
    : Stream.Filter S
  :=
    { filter, subStream }
end filter



section map
  structure Stream.Map
    (S : Type u)
    [Stream S α]
    (β : Type v)
  where
    map : α → β
    subStream : S

  partial def Stream.Map.next?
    [Stream S α]
    (self : Stream.Map S β)
    : Option (β × Stream.Map S β)
  :=
    match Stream.next? self.subStream with
    | none => none
    | some (next, subStream) =>
      some (self.map next, { self with subStream })
  
  instance streamMap [Stream S α] : Stream (Stream.Map S β) β where
    next? self := self.next?

  def Stream.map
    [Stream S α]
    (subStream : S) (map: α → β)
    : Stream.Map S β
  :=
    { map, subStream }
end map

section filterMap
  structure Stream.FilterMap
    (S : Type u)
    [Stream S α]
    (β : Type v)
  where
    filterMap : α → Option β
    subStream : S

  partial def Stream.FilterMap.next?
    [Stream S α]
    (self : Stream.FilterMap S β)
    : Option (β × Stream.FilterMap S β)
  :=
    match Stream.next? self.subStream with
    | none => none
    | some (next, subStream) =>
      let self := { self with subStream }
      match self.filterMap next with
      | none => self.next?
      | some b => some (b, self)
  
  instance streamFilterMap [Stream S α] {β : Type u} : Stream (Stream.FilterMap S β) β where
    next? := Stream.FilterMap.next?
  
  def Stream.filterMap
    [Stream S α]
    (subStream : S)
    (filterMap : α → Option β)
    : Stream.FilterMap S β
  :=
    { subStream, filterMap }
end filterMap

section merge
  structure Stream.Merge
    (S₁ S₂ : Type u)
    [Stream S₁ α] [Stream S₂ α]
  where
    subStream₁ : S₁
    subStream₂ : S₂
    decideNext : α → α → Bool

  partial def Stream.Merge.next?
    [Stream S₁ α] [Stream S₂ α]
    (self : Stream.Merge S₁ S₂)
    : Option (α × Stream.Merge S₁ S₂)
  :=
    match (Stream.next? self.subStream₁, Stream.next? self.subStream₂) with
    | (none, none) =>
      none
    | (some (a, subStream₁), none) =>
      some (a, {self with subStream₁})
    | (none, some (a, subStream₂)) =>
      some (a, {self with subStream₂})
    | (some (a₁, subStream₁), some (a₂, subStream₂)) =>
      if self.decideNext a₁ a₂ then
        some (a₁, {self with subStream₁})
      else
        some (a₂, {self with subStream₂})
  
  instance streamMerge
    [Stream S₁ α] [Stream S₂ α]
    : Stream (Stream.Merge S₁ S₂) α
  where
    next? := Stream.Merge.next?
  
  def Stream.merge
    [Stream S₁ α] [Stream S₂ α]
    (subStream₁ : S₁) (subStream₂ : S₂)
    (decideNext : α → α → Bool)
    : Stream.Merge S₁ S₂
  :=
    { subStream₁, subStream₂, decideNext }
end merge



section zip
  structure Stream.Zip
    (S₁ : Type u)
    (S₂ : Type v)
    [Stream S₁ α]
    [Stream S₂ β]
  where
    subStream₁ : S₁
    subStream₂ : S₂

  partial def Stream.Zip.next?
    [Stream S₁ α]
    [Stream S₂ β]
    (self : Stream.Zip S₁ S₂)
    : Option ((α × β) × Stream.Zip S₁ S₂)
  :=
    match (Stream.next? self.subStream₁, Stream.next? self.subStream₂) with
    | (none, _) | (_, none) => none
    | (
      some (next₁, subStream₁),
      some (next₂, subStream₂)
    ) =>
      let self := { self with subStream₁, subStream₂ }
      some ((next₁, next₂), self)
  
  instance
    [Stream S₁ α] [Stream S₂ β]
    : Stream (Stream.Zip S₁ S₂) (α × β)
  where
    next? := Stream.Zip.next?
  
  def Stream.zip
    [Stream S₁ α] [Stream S₂ β]
    (subStream₁ : S₁) (subStream₂ : S₂)
    : Zip S₁ S₂
  :=
    { subStream₁, subStream₂ }
end zip

structure StreamOf (α : Type u) where
  protected innerMk ::
    S : Type v
    streamS : Stream S α
    stream : S

def StreamOf.mk {S : Type v} (stream : S) [inst : Stream S α] : StreamOf α :=
  StreamOf.innerMk S inst stream

instance functorStreamOf : Functor StreamOf where
  map {α β} aToB streamOfA :=
    let hint := streamOfA.streamS
    Stream.map streamOfA.stream aToB
    |> StreamOf.mk

instance pureStreamOf : Pure StreamOf where
  pure {α} a :=
    let const : Stream.Const a := Stream.Const.mk
    StreamOf.mk const

instance seqStreamOf : Seq StreamOf where
  seq {α β} fAToB getFA :=
    let hint₁ := fAToB.streamS
    let fA := getFA ()
    let hint₂ := fA.streamS
    let zipped := Stream.zip fAToB.stream fA.stream
    let mapped := Stream.map zipped (fun (f, a) => f a)
    StreamOf.mk mapped

instance seqLeftStreamOf : SeqLeft StreamOf where
  seqLeft {α β} fA getFB :=
    fA

instance seqRightStreamOf : SeqRight StreamOf where
  seqRight {α β} fA getFB :=
    getFB ()

instance applicativeStreamOf : Applicative StreamOf where
  toFunctor := functorStreamOf
  toPure := pureStreamOf
  toSeq := seqStreamOf
  toSeqLeft := seqLeftStreamOf
  toSeqRight := seqRightStreamOf


