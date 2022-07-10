

/-! # Basic types

-/



namespace Err



/-! ## Random useful stuff -/

/-- `K` combinator, discards its input and returns `val`. -/
def 𝕂 (val : β) : α → β :=
  fun _ => val

/-- Lazyfies a term. -/
macro:max "lazy! " t:term : term =>
  `(fun _ => $t)
macro:max "lazy_s! " str:interpolatedStr(term) : term =>
  `(fun _ => s!$str)

def List.revAppend (self : List α) (l : List α) : List α :=
  match l with
  | [] => self
  | hd::tl =>
    revAppend (hd :: self) tl



/-! ## Conversion typeclass -/

/-- Converts an `α` into a `β`.

`Into α α` for all `α` is provided, along with a few others.
-/
class Into (α : Type u) (β : Type v) where
  conv : α → β

export Into (conv)

instance instIntoSelf : Into α α where
  conv :=
    id

instance instIntoToString [ToString α] : Into α String where
  conv :=
    toString

instance instIntoOption : Into α (Option α) where
  conv :=
    some

instance instIntoFunctor
  {F : Type u → Type v}
  [Functor F]
  [C : Into α β]
  : Into (F α) (F β)
where
  conv :=
    Functor.map C.conv



/-! ## List/string creation by repeating a value -/

--- `[a, a, ...]` repeating `n` times.
protected def List.repeat (a : α) : Nat → List α
  | 0 => []
  | n + 1 => a :: List.repeat a n
--- `⟨[c, c, ...]⟩` repeating `n` times.
protected def String.repeat (c : Char) (n : Nat) : String :=
  ⟨List.repeat c n⟩



/-! ## Styling, used for displaying fancy errors -/

/-- Stores styling functions, typically using ANSI escape codes.

The `Inhabited.default` performs no styling, *i.e.* all functions are `id`.
-/
structure Style where
  --- Fatal text (red).
  fatal : String → String
  --- Bad text (yellow).
  bad : String → String
  --- Good text (green).
  good : String → String
  --- Bold.
  bold : String → String
  --- Italic.
  ita : String → String
  --- Underlined.
  uline : String → String

--- Does not do any styling.
instance instInhabitedStyle : Inhabited Style where
  default :=
    ⟨id, id, id, id, id, id⟩

namespace Style
  /-- Markdown-like style. -/
  def md : Style where
    bold s :=
      s!"**{s}**"
    ita s :=
      s!"*{s}*"
    uline s :=
      s!"__{s}__"
    fatal s :=
      s!"**{s}**"
    bad s :=
      s!"*{s}*"
    good s :=
      s
end Style



/-! ## Styling (pretty-printing) -/



/-- Styles itself to `String` and `Std.Format` (multiline).

A few instances are provided:
- `ToStyled String`
- `Repr ε ⇒ ToStyled ε`
- `ToString ε ⇒ ToStyled ε`
All of them ignore their `Style` parameter.
-/
class Style.ToStyled (ε : Type u) where
  --- Styles itself to `String` (multiline).
  toStyled : ε → Style → String
  --- Sytles itself to `Std.Format` (multiline), same as `toStyled` by default.
  toStyledRepr : ε → Style → Nat → Std.Format :=
    fun e s _ =>
      toStyled e s
      |> Std.Format.text

/-- Convenience `Style.ToStyled.toStyled` alias. -/
abbrev Style.toStyled [S : Style.ToStyled α] :=
  S.toStyled
/-- Convenience `Style.ToStyled.toStyledRepr` alias. -/
abbrev Style.toStyledRepr [S : Style.ToStyled α] :=
  S.toStyledRepr



/-! ### Automatic `ToStyled` instances -/

--- `ToStyled String`.
instance instToStyledString : Style.ToStyled String where
  toStyled s _ :=
    s

--- `Repr → ToStyled`.
instance instToStyledRepr [Repr ε] : Style.ToStyled ε where
  toStyled e _ :=
    s!"{reprPrec e 1}"
  toStyledRepr e _ prec :=
    reprPrec e prec

--- Generates a `ToStyled` from a `Repr`.
def Style.ToStyled.ofRepr :=
  @instToStyledRepr

--- `ToString → ToStyled`.
instance instToStyledToString [ToString ε] : Style.ToStyled ε where
  toStyled s _ :=
    toString s

--- Generates a `ToStyled` from a `ToString`.
def Style.ToStyled.ofToString :=
  @instToStyledToString



/-! ### Convenience printing instances derived from `ToStyled`  -/



--- `ToStyled → ToString`
instance instToStringToStyled [Style.ToStyled ε] : ToString ε where
  toString e :=
    s!"{Style.ToStyled.toStyledRepr e default 1}"
--- `ToStyled → Repr`
instance instReprToStyled [Style.ToStyled ε] : Repr ε where
  reprPrec e prec :=
    s!"{Style.ToStyled.toStyledRepr e default prec}"
