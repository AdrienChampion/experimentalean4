import Err.Err

/-! # Result monad
-/



namespace Err



/-- Just the result monad. -/
inductive Res (γ : Type u) (ε : Type v) (α : Type w)
  --- Nominal case.
  | ok : α → Res γ ε α
  --- Error case
  | err : Err γ ε → Res γ ε α
deriving Inhabited

/-- Produces an error. -/
def Res.bail [Into ε' ε] (source : ε') : Res γ ε α :=
  conv source
  |> Err.mk
  |> err

export Res (ok err bail)

namespace Res
  variable
    {ε : Type u}
    {α : Type v}

  /-- Map over the error value. -/
  def mapErr (f : Err γ ε → Err γ' ε') : Res γ ε α → Res γ' ε' α
    | ok a => ok a
    | err e => f e |> err

  /-- Map over the inner error value. -/
  def mapInnerErr (f : ε → ε') : Res γ ε α → Res γ ε' α
    | ok a => ok a
    | err e => e.mapSource f |> err
  /-- Map over the inner context bits. -/
  def mapInnerContext (f : γ → γ') : Res γ ε α → Res γ' ε α
    | ok a => ok a
    | err e => e.mapContext f |> err

  /-- True if `ok`. -/
  def isOk : Res γ ε α → Bool
    | ok _ => true
    | err _ => false
  /-- True if `err`. -/
  def isErr : Res γ ε α → Bool :=
    not ∘ isOk

  /-- Abbreviation for `isOk`. -/
  abbrev toBool :=
    @isOk



  /-- Lazily adds context to errors. -/
  def withContext [Into γ' γ] (ctx : Unit → γ') : Res γ ε α → Res γ ε α
    | ok a =>
      ok a
    | err e =>
      ctx ()
      |> e.context
      |> err

  /-- Eagerly adds context to errors. -/
  def context [Into γ' γ] (ctx : γ') : Res γ ε α → Res γ ε α
    | ok a =>
      ok a
    | err e =>
      e.context ctx
      |> err


  /-! ## Monadic operations -/

  def map (f : α → β) : Res γ ε α → Res γ ε β
    | ok a => f a |> ok
    | err e => err e

  def pure : α → Res γ ε α :=
    ok

  def bind : Res γ ε α → (α → Res γ ε β) → Res γ ε β
    | ok a => (· a)
    | err e => err e |> 𝕂
end Res

--- Let's do this.
instance instMonadRes : Monad (Res γ ε) where
  pure :=
    Res.pure
  bind :=
    Res.bind



/-! ## (Pretty-)Printing instances -/

instance instToStringRes
  [ToString γ]
  [ToString ε]
  [ToString α]
  : ToString (Res γ ε α)
where
  toString
    | Res.ok a => toString a
    | Res.err e => toString e

instance instReprRes
  [Repr γ]
  [Repr ε]
  [Repr α]
  : Repr (Res γ ε α)
where
  reprPrec
    | Res.ok a => reprPrec a
    | Res.err e => reprPrec e



/-! ## Other instances -/

instance instToBoolRes : ToBool (Res γ ε α) where
  toBool :=
    Res.toBool
