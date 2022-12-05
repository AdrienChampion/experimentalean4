


namespace Stream2



/-- A list with a lazy tail. -/
inductive Stream (α : Type u)
  -- Empty stream
  | noth : Stream α
  -- The head of the stream and its lazy tail.
  | cons : α → (Unit → Stream α) → Stream α
deriving Inhabited

namespace Stream
  /-- Same as [`noth`]. -/
  protected abbrev none {α : outParam (Type u)} : Stream α :=
    noth

  /-- A single element and then nothing. -/
  abbrev one : α → Stream α :=
    (cons · fun _ => noth)

  /-- A value repeated `n` times. -/
  def many (val : α) : Nat → Stream α
    | 0 =>
      noth
    | n + 1 =>
      let tl _ := many val n
      cons val tl
  
  /-- Creates a stream using a generator.
  
  - Stops at the first `none` value.
  -/
  partial def generate (gen : Nat → Option α) : Stream α :=
    loop 0
  where
    loop n :=
      if let some val := gen n then
        let tl _ := n + 1 |> loop
        cons val tl
      else noth

  /-- Produces the value `a` forever. -/
  partial def always (a : α) : Stream α :=
    let tl _ := always a
    cons a tl

  /-- Same as [`always`]. -/
  def pure := @always

  /-- Turns a list into a stream. -/
  def ofList : List α → Stream α
    | [] => noth
    | hd :: tl => cons hd fun _ => ofList tl

  /-- Concatenates two streams. -/
  partial def concat : Stream α → Stream α → Stream α
    | noth, s => s
    | s, noth => s
    | cons hd₁ tl₁, s₂ =>
      cons hd₁ fun () => tl₁ () |>.concat s₂

  /-- Lazy version of [`concat`]. -/
  partial def lconcat : Stream α → (Unit → Stream α) → Stream α
    | noth, s₂ => s₂ ()
    | cons hd₁ tl₁, s₂ =>
      cons hd₁ fun () => tl₁ () |>.lconcat s₂

  /-- Flattens a stream of streams. -/
  partial def flatten : Stream (Stream α) → Stream α
    | noth => noth
    | cons hd tl =>
      hd.lconcat fun _ => tl () |>.flatten

  /-- Filter-map over streams.

  - Filtering can make [`next`]-like functions loop forever on infinite streams.
  -/
  partial def filterMap (f : α → Option β) : Stream α → Stream β
    | noth => noth
    | cons hd tl =>
      let tl _ :=
        tl () |>.filterMap f
      if let some hd := f hd
      then cons hd tl
      else tl ()

  /-- Plain old map. -/
  partial def map (f : α → β) (self : Stream α) : Stream β :=
    self.filterMap
      fun a => f a

  /-- Sure, why not. -/
  partial def bind
    {α β : Type u}
    (self : Stream α)
    (f : α → Stream β)
  : Stream β :=
    self.map f |>.flatten

  /-- Filters values in a stream.

  - Filtering can make [`next`]-like functions loop forever on infinite streams.
  -/
  partial def filter (f : α → Bool) (self : Stream α) : Stream α :=
    self.filterMap
      fun a => if f a then a else none

  /-- True if empty. -/
  @[simp]
  abbrev isEmpty : Stream α → Prop
    | noth => True
    | cons _ _ => False
end Stream

/-- [`Stream.isEmpty`] is decidable. -/
instance instDecidableStreamIsEmpty
  {s : Stream α}
: Decidable s.isEmpty :=
  open Stream in
  match h : s with
  | noth =>
    isTrue (by simp [h, isEmpty])
  | cons _ _ =>
    isFalse fun _ => by contradiction

namespace Stream
  /-- Next element. -/
  def next
    (self : Stream α)
    (nempty : ¬ self.isEmpty := by simp ; try assumption)
  : α × Stream α :=
    match self with
    | noth =>
      by simp [isEmpty] at nempty
    | cons head tail =>
      (head, tail ())

  /-- Next element, if any. -/
  def next? (self : Stream α) : Option α × Stream α :=
    if h : self.isEmpty then (none, self) else self.next.map some id

  /-- Next element, panics if `none`. -/
  def next!
    [Inhabited α]
    (self : Stream α)
  : α × Stream α :=
    if h : self.isEmpty then
      panic! "called `Stream.next!` on an empty `Stream` :/"
    else self.next

  /-- Produces the `n` first elements of a stream as a list. -/
  def take : Nat → Stream α → List α × Stream α
    | 0, s | _, s@noth => ([], s)
    | n + 1, cons hd tl =>
      let (l, s) :=
        tl () |>.take n
      (hd :: l, s)

  /-- Same as [`take`] but discards the result stream. -/
  def just (n : Nat) (self : Stream α) : List α :=
    self.take n |>.1

  #eval
    Stream.always 7
    |>.concat (Stream.always 8)
    |>.map (fun svn => svn + 3)
    |>.just 7

  #eval
    Stream.ofList [1, 2, 3, 4, 5, 6]
    |>.concat (Stream.always 6)
    |>.filterMap
      (fun n => if n%2 = 0 then some n else none)
    |>.just 5
end Stream

/-- It's a functor now `\(*o*)/` -/
instance instFunctorStream : Functor Stream where
  map := Stream.map

/-- It's a monad now `\(*o*)/` -/
instance instMonadStream : Monad Stream where
  pure := Stream.pure
  bind := Stream.bind