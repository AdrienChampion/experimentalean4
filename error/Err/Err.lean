import Err.Init

/-! # The `Err` structure stores a source error and a trace
-/



namespace Err



structure Err (ε : Type u) where
protected mkAux ::
  source : ε
  trace : List ε

namespace Err
  variable
    {ε : Type u}
    (self : Err ε)

  def mk (source : ε) : Err ε :=
    ⟨source, []⟩
  
  def context [Into α ε] (err : α) : Err ε :=
    { self with trace := conv err :: self.trace }

  def split : Err ε → ε × List ε
    | ⟨source, []⟩ =>
      (source, [])
    | ⟨source, head :: tail⟩ =>
      (head, tail ++ [source])

  def foldl (f : α → ε → α) (init : ε → α) : α :=
    let (head, tail) :=
      self.split
    init head
    |> tail.foldl f

  def toStyledRepr
    [E : Style.ToStyled ε]
    (style : Style)
    (prec : Nat)
    (pref : optParam String "- ")
    : Std.Format
  :=
    self.foldl concat init
  where
    init err :=
      E.toStyledRepr err style prec
      |> Std.Format.nest 2
    concat fmt err :=
      let text :=
        pref ++ E.toStyledRepr err style prec
        |> Std.Format.nest 2
      f!"{fmt}\n{text}"

  def reprPrec
    [E : Repr ε]
    (prec : Nat)
    (pref : optParam String "- ")
    : Std.Format
  :=
    self.foldl concat init
  where
    init err :=
      E.reprPrec err prec
      |>.nest 2
    concat fmt err :=
      let text :=
        pref ++ E.reprPrec err prec
        |>.nest 2
      f!"{fmt}\n{text}"

  def toStyledString
    [E : Style.ToStyled ε]
    (style : Style)
    (indentCount : optParam Nat 0)
    (pref : optParam String "- ")
    : String
  :=
    self.foldl concat init
  where
    indent :=
      String.repeat ' ' indentCount
    init err :=
      E.toStyled err style
    concat str err :=
      s!"{str}\n{indent}{pref}{E.toStyled err style}"

  def toString
    [E : ToString ε]
    (indentCount : optParam Nat 0)
    (pref : optParam String "- ")
    : String
  :=
    self.foldl concat init
  where
    indent :=
      String.repeat ' ' indentCount
    init err :=
      E.toString err
    concat str err :=
      s!"{str}\n{indent}{pref}{E.toString err}"
end Err



/-! ## Basic instances -/

instance instIntoErr [Into ε' ε] : Into ε' (Err ε) where
  conv :=
    Err.mk ∘ conv



/-! ## (Pretty-)printing -/

instance instToStringErr [ToString ε] : ToString (Err ε) where
  toString :=
    Err.toString

instance instReprErr [Repr ε] : Repr (Err ε) where
  reprPrec :=
    Err.reprPrec

instance instToStyledErr [Style.ToStyled ε] : Style.ToStyled (Err ε) where
  toStyled :=
    Err.toStyledString
  toStyledRepr :=
    Err.toStyledRepr



/-! ## `Functor` and `Pure` -/

namespace Err
  def pure (a : α) :=
    Err.mk a

  def map (f : α → β) : Err α → Err β
    | ⟨source, trace⟩ =>
      ⟨f source, trace.map f⟩
end Err

instance instFunctorErr : Functor Err where
  map :=
    Err.map

instance instPureErr : Pure Err where
  pure :=
    Err.pure
