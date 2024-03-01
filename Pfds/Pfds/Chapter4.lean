import Pfds.Init


/-! # Chapter 4 -/
namespace Pfds.C4



/-! ## Streams

Implemented using `Thunk`-s. Note that `Pfds.Init` extends `Thunk`-s with

- a `lazy $t` notation that wraps `$t` in (a computation in) a `Thunk`, and
- `Monad Thunk` and `LawfulMonad Thunk` instances.
-/


mutual
  inductive StreamCell (α : Type) : Type
  | nil
  | cons : α → Stream α → StreamCell α
  deriving Inhabited

  inductive Stream (α : Type) : Type
  | mk : Thunk (StreamCell α) → Stream α
  deriving Inhabited
end

namespace StreamCell
  /-- `StreamCell`'s `nil` constructor. -/
  scoped notation "[!]" => StreamCell.nil
  /-- `StreamCell`'s node `cons`tructor. -/
  scoped infixr:67 " !:: " => StreamCell.cons
end StreamCell

open scoped StreamCell

namespace Stream
  /-- Builds a `Thunk` (lazily) evaluating to a term. -/
  syntax:max "stream! " term : term

  macro_rules
  | `(stream! $t) => `(Stream.mk $ Thunk.mk fun _ => $t)

  protected abbrev nil : Stream α :=
    stream! [!]
  protected abbrev cons (hd : α) (tl : Stream α) : Stream α :=
    stream! hd !:: tl

  /-- An empty `Stream`. -/
  scoped notation "[~]" => Stream.nil
  /-- Prepends a value at the beginning of a `Stream`, and does so **eagerly**. -/
  scoped infixr:67 " ~:: " => Stream.cons

  def cell : Stream α → Thunk (StreamCell α)
  | mk cell => cell

  def getCell : Stream α → StreamCell α :=
    Thunk.get ∘ cell

  instance instCoeThunk : Coe (Stream α) (Thunk (StreamCell α)) where
    coe := cell
  instance instCoeOfThunk : Coe (Thunk (StreamCell α)) (Stream α) where
    coe := mk
end Stream

open scoped Stream

protected partial def StreamCell.pure (a : α) : StreamCell α :=
  a !:: [~]

protected partial def Stream.pure : α → Stream α :=
  (lazy StreamCell.pure ·)

-- `map`
mutual
  protected partial def StreamCell.map (f : α → β) : StreamCell α → StreamCell β
  | .nil => .nil
  | .cons hd tl => .cons (f hd) (tl.map f)

  protected partial def Stream.map (f : α → β) (s : Stream α) : Stream β :=
    lazy s.getCell.map f
end

namespace Stream
  def branch (f_nil : Unit → β) (f_cons : α → Stream α → β) (s : Stream α) : Thunk β := do
    if let .cons hd tl ← s.cell
    then f_cons hd tl
    else f_nil ()

  def branchMap
    (f_nil : Unit → StreamCell β)
    (f_cons : α → Stream α → StreamCell β)
    (s : Stream α)
  : Stream β := .mk do
    if let .cons hd tl ← s.cell
    then f_cons hd tl
    else f_nil ()

  def consMap
    (f_cons : α → Stream α → StreamCell β)
    (s : Stream α)
  : Stream β :=
    s.branchMap (𝕂 .nil) f_cons


  partial def append (s₁ s₂ : Stream α) : Stream α :=
    s₁.branchMap
      (f_nil := 𝕂 s₂.getCell)
      (f_cons := fun hd tl => .cons hd (tl.append s₂))

  instance instAppend : Append (Stream α) where
    append := append



  def take : Nat → Stream α → Stream α
  | 0, _ =>
    .mk lazy .nil
  | n + 1, s =>
    s.consMap fun hd tl => hd !:: (tl.take n)

  partial def takeToList (n : Nat) (s : Stream α) : List α :=
    aux n s.getCell
  where
    aux : Nat → StreamCell α → List α
    | 0, _
    | _, [!] => .nil
    | n + 1, hd !:: tl => hd :: (aux n $ tl.getCell)

  #guard [~].takeToList 0 = ([] : List Unit)
  #guard [~].takeToList 10 = ([] : List Unit)
  #guard (0~::0~::0~::0~::0~::[~]).takeToList 0 = []
  #guard (0~::0~::0~::0~::0~::[~]).takeToList 1 = [0]
  #guard (0~::0~::0~::0~::0~::[~]).takeToList 3 = [0, 0, 0]
  #guard (0~::0~::0~::0~::0~::[~]).takeToList 5 = [0, 0, 0, 0, 0]
  #guard (0~::0~::0~::0~::0~::[~]).takeToList 9 = [0, 0, 0, 0, 0]



  partial def drop (n : Nat) (s : Stream α) : Stream α := .mk lazy
    match (n, s.getCell) with
    | (0, c) => c
    | (_, .nil) => .nil
    | (n + 1, _hd !:: tl) =>
      (tl.drop n).getCell

  def getVal (s : Stream α) : Option α :=
    if let hd !:: _ := s.getCell
    then hd else none

  partial def get : Nat → Stream α → Option α
  | 0, s => s.getVal
  | n + 1, s =>
    if let _ !:: s := s.getCell
    then s.get n else none

  /-- Reverses a stream, will not be able to yield values on infinite streams. -/
  partial def reverse : Stream α → Stream α :=
    aux [~]
  where
    aux (acc s : Stream α) : Stream α :=
      s.branchMap
        (fun _ => acc.getCell)
        (fun hd tl =>
          let acc := hd ~:: acc
          aux acc tl |>.getCell)


  partial def forever (val : α) : Stream α := .mk lazy
    .cons val (forever val)

  #guard (forever 0).takeToList 7 = List.replicate 7 0
  #guard (forever 0).takeToList 10 = List.replicate 10 0



  partial def fib : Stream Nat :=
    1 ~:: 1 ~:: aux 1 1
  where
    aux (pre₂ pre₁ : Nat) : Stream Nat := .mk lazy
      let val := pre₂ + pre₁
      .cons val (aux pre₁ val)

  #guard fib.takeToList 10 = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55]
  #guard (fib.take 10 |>.reverse |>.takeToList 20) = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55].reverse

  partial def fact : Stream Nat :=
    1 ~:: aux 1 1
  where
    aux (pre idx : Nat) : Stream Nat := .mk lazy
      let val := pre * idx
      .cons val (aux val idx.succ)

  #guard fact.takeToList 7 = [1, 1, 2, 6, 24, 120, 720]
end Stream
