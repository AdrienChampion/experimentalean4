import Err.Err

/-! # Result monad
-/



namespace Err



/-- Just the result monad. -/
inductive Res (ε : Type v) (α : Type w)
  --- Nominal case.
  | ok : α → Res ε α
  --- Error case
  | err : ε → Res ε α
deriving Inhabited

/-- Produces an error. -/
def Res.bail [Into ε' ε] (e : ε') : Res ε α :=
  conv e
  |> err

export Res (ok err bail)

namespace Res
  /-- Map over the error value. -/
  def mapErr (f : ε → ε') : Res ε α → Res ε' α
    | ok a => ok a
    | err e => f e |> err

  /-- Map over the inner error value. -/
  def mapInnerErr (f : ε → ε') : Res (Err γ ε) α → Res (Err γ ε') α
    | ok a => ok a
    | err e => e.mapSource f |> err
  /-- Map over the inner context bits. -/
  def mapInnerContext (f : γ → γ') : Res (Err γ ε) α → Res (Err γ' ε) α
    | ok a => ok a
    | err e => e.mapContext f |> err

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
  def withContext [Into γ' γ] (ctx : Unit → γ') : Res (Err γ ε) α → Res (Err γ ε) α
    | ok a =>
      ok a
    | err e =>
      ctx ()
      |> e.context
      |> err

  /-- Eagerly adds context to errors. -/
  def context [Into γ' γ] (ctx : γ') : Res (Err γ ε) α → Res (Err γ ε) α
    | ok a =>
      ok a
    | err e =>
      e.context ctx
      |> err


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

-- Let's do this.
instance instMonadRes : Monad (Res ε) where
  pure :=
    Res.pure
  bind :=
    Res.bind



/-! ## (Pretty-)Printing instances -/

instance instToStringRes
  [ToString ε]
  [ToString α]
  : ToString (Res ε α)
where
  toString
    | Res.ok a => toString a
    | Res.err e => toString e

instance instReprRes
  [Repr ε]
  [Repr α]
  : Repr (Res ε α)
where
  reprPrec
    | Res.ok a => reprPrec a
    | Res.err e => reprPrec e



/-! ## Other instances -/

instance instToBoolRes : ToBool (Res ε α) where
  toBool :=
    Res.toBool
