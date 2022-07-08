import Err.Res

/-! # Monad transformer for `Res` -/



namespace Err



/-- Monad transformer -/
abbrev ResT
  (ε : Type u)
  (μ : Type (max u v) → Type w)
  (α : Type v)
  : Type w
:=
  μ (Res ε α)



namespace ResT
  variable
    {γ : Type u}
    {γ' : Type u}
    {ε : Type u}
    {ε' : Type u}
    {μ : Type (max u v) → Type w}
    {α : Type v}
    {β : Type v}

  /-! ## Basic functions

      Note that `run` and `mk` are totally stolen from Lean's `OptionT`.
  -/

  /-- Turns a `ResT _ μ` into a `μ Res`. -/
  @[inline]
  def run (a? : ResT ε μ α) : μ (Res ε α) :=
    a?

  /-- Turns a `μ Res` into a `ResT _ μ` -/
  def mk (a? : μ (Res ε α)) : ResT ε μ α :=
    a?

  /-- Map over the nominal value. -/
  def map
    [Fun : Functor μ]
    (f : α → β)
  : ResT ε μ α → ResT ε μ β
  :=
    Fun.map (Res.map f)

  /-- Map over the error value. -/
  def mapErr
    [Fun : Functor μ]
    (f : ε → ε')
  : ResT ε μ α
    → ResT ε' μ α
  :=
    Fun.map (Res.mapErr f)

  /-- Map over the inner error value. -/
  def mapInnerErr
    [Fun : Functor μ]
    (f : ε → ε')
    : ResT (Err γ ε) μ α
    → ResT (Err γ ε') μ α
  :=
    Res.mapInnerErr f
    |> Fun.map
  /-- Map over the inner context bits. -/
  def mapInnerContext
    [Fun : Functor μ]
    (f : γ → γ')
    : ResT (Err γ ε) μ α
    → ResT (Err γ' ε) μ α
  :=
    Res.mapInnerContext f
    |> Fun.map



  /-! ## Monadic functions -/

  @[inline]
  def pure
    [Mon : Monad μ]
    (a : α)
    : ResT ε μ α
  :=
    ok a
    |> Mon.pure

  @[inline]
  def bind
    [Mon : Monad μ]
    (a? : ResT ε μ α)
    (f? : α → ResT ε μ β)
    : ResT ε μ β
  :=
    mk do
      match ← a? with
      | ok a => f? a
      | err e => err e |> Mon.pure
end ResT

instance instMonadResT [Monad μ] : Monad (ResT ε μ) where
  pure :=
    ResT.pure
  bind :=
    ResT.bind
