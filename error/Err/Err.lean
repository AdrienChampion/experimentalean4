import Err.Init

/-! # The `Err` structure stores a source error and a trace
-/



namespace Err



structure Err (γ : Type u) (ε : Type v) where
protected mkAux ::
  source : ε
  trace : List γ

namespace Err
  variable
    {γ : Type u}
    {ε : Type v}
    (self : Err γ ε)

  /-- Constructor. -/
  def mk (source : ε) : Err γ ε :=
    ⟨source, []⟩

  /-- Adds some context to an error. -/
  def context [Into γ' γ] (err : γ') : Err γ ε :=
    { self with trace := conv err :: self.trace }

  /-- Map over the underlying error. -/
  def mapSource (f : ε → ε') : Err γ ε' :=
    { self with source := f self.source }
  /-- Map over the context bits. -/
  def mapContext (f : γ → γ') : Err γ' ε :=
    { self with trace := self.trace.map f }

  def toStyledRepr
    [instε : Style.ToStyled ε]
    [instγ : Style.ToStyled γ]
    (style : Style)
    (prec : Nat)
    (pref : optParam String "- ")
    : Std.Format
  :=
    let source :=
      (pref ++ instε.toStyledRepr self.source style prec)
      |>.nest 2
    match self.trace with
    | [] =>
      source
    | hd::tl =>
      (pref ++ instγ.toStyledRepr hd style prec)
      |>.nest 2
      |> tl.foldl
        fun acc ctx =>
          acc ++ (
            (pref ++ instγ.toStyledRepr ctx style prec)
            |>.nest 2
          )

  def reprPrec
    [Style.ToStyled ε]
    [Style.ToStyled γ]
    (prec : Nat)
    (pref : optParam String "- ")
    : Std.Format
  :=
    self.toStyledRepr default prec pref
    

  def toStyledString
    [Style.ToStyled ε]
    [Style.ToStyled γ]
    (style : Style)
    (prec : optParam Nat 1)
    (pref : optParam String "- ")
    : String
  :=
    s!"{self.toStyledRepr style prec pref}"

  def toString
    [Style.ToStyled ε]
    [Style.ToStyled γ]
    (prec : optParam Nat 1)
    (pref : optParam String "- ")
    : String
  :=
    self.toStyledString default prec pref
end Err



/-! ## Basic instances -/

instance instIntoErr [Into ε' ε] : Into ε' (Err γ ε) where
  conv :=
    Err.mk ∘ conv



/-! ## (Pretty-)printing -/

instance instToStyledErr
  [Style.ToStyled ε] [Style.ToStyled γ]
  : Style.ToStyled (Err γ ε)
where
  toStyled :=
    Err.toStyledString
  toStyledRepr :=
    Err.toStyledRepr



/-! ## `Functor` and `Pure` -/

namespace Err
  def pure (a : ε) : Err γ ε :=
    Err.mk a

  def map (f : ε → ε') (self : Err γ ε) :  Err γ ε' :=
    { self with source := f self.source }
end Err

instance instFunctorErr : Functor (Err γ) where
  map :=
    Err.map

instance instPureErr : Pure (Err γ) where
  pure :=
    Err.pure
