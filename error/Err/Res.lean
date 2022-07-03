import Err.Err

/-! # Result monad
-/



namespace Err



/-- Just the result monad. -/
inductive Res (ε : Type u) (α : Type v)
  --- Nominal case.
  | ok : α → Res ε α
  --- Error case
  | err : Err ε → Res ε α
deriving Inhabited

/-- Produces an error. -/
def Res.bail [Into ε' ε] (source : ε') : Res ε α :=
  conv source
  |> Err.mk
  |> err

export Res (ok err bail)

namespace Res
  variable
    {ε : Type u}
    {α : Type v}

  /-- Map over the error value. -/
  def mapErr (f : Err ε → Err ε') : Res ε α → Res ε' α
    | ok a => ok a
    | err e => f e |> err

  /-- Map over the inner error value. -/
  def mapInnerErr (f : ε → ε') : Res ε α → Res ε' α
    | ok a => ok a
    | err e => e.map f |> err

  /-- True if `ok`. -/
  def isOk : Res ε α → Bool
    | ok _ => true
    | err _ => false
  /-- True if `err`. -/
  def isErr : Res ε α → Bool :=
    not ∘ isOk

  /-- Abbreviation for `isOk`. -/
  abbrev toBool :=
    @isOk



  /-- Lazily adds context to errors. -/
  def withContext [Into ε' ε] (ctx : Unit → ε') : Res ε α → Res ε α
    | ok a => ok a
    | err e =>
      ctx ()
      |> e.context
      |> err

  /-- Eagerly adds context to errors. -/
  def context [Into ε' ε] (ctx : ε') : Res ε α → Res ε α
    | ok a => ok a
    | err e => e.context ctx |> err


  /-! ## Monadic operations -/

  def map (f : α → β) : Res ε α → Res ε β
    | ok a => f a |> ok
    | err e => err e

  def pure : α → Res ε α :=
    ok

  def bind : Res ε α → (α → Res ε β) → Res ε β
    | ok a => (· a)
    | err e => err e |> 𝕂
end Res

--- Let's do this.
instance instMonadRes : Monad (Res ε) where
  pure :=
    Res.pure
  bind :=
    Res.bind



/-! ## (Pretty-)Printing instances -/

instance instToStringRes [ToString α] [ToString ε] : ToString (Res ε α) where
  toString
    | Res.ok a => toString a
    | Res.err e => toString e

instance instReprRes [Repr α] [Repr ε] : Repr (Res ε α) where
  reprPrec
    | Res.ok a => reprPrec a
    | Res.err e => reprPrec e



/-! ## Other instances -/

instance instToBoolRes : ToBool (Res ε α) where
  toBool :=
    Res.toBool
