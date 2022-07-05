import Err

/-! # `Res String α` example -/



namespace Err.Examples.String



abbrev Res :=
  Err.Res String String
abbrev ErrStateT :=
  Err.ErrStateT String String
abbrev ErrStateM :=
  Err.ErrStateM String String

abbrev resOf (source : String) (trace : optParam (List String) []) : Res α :=
  ⟨source, trace⟩
  |> err



abbrev div? (a b : Nat) : Res Nat :=
  do
    if b = 0 then
      bail s!"cannot divide `{a}` by `{b}`"
    return a / b

example :
  div? 7 0 = resOf "cannot divide `7` by `0`"
:= rfl



@[simp]
abbrev divAddDiv? (a b c d : Nat) : Res Nat :=
  do
    let d₁ ←
      div? a b
      |>.withContext lazy_s!"cannot compute `{a}/{b} + {c}/{d}`"
    let d₂ ←
      div? c d
      |>.withContext lazy_s!"cannot compute `{a}/{b} + {c}/{d}"
    return d₁ + d₂

example :
  divAddDiv? 7 0 3 2
  =
  resOf "cannot divide `7` by `0`" ["cannot compute `7/0 + 3/2`"]
:= rfl



-- Don't know how to prove this :/

-- example :
--   divAddDiv? 7 2 3 0
--   =
--   resOf "cannot divide `3` by `0`" ["cannot compute `7/2 + 3/0`"]
-- := by
--   simp [
--     divAddDiv?, div?,
--     Res.withContext, Res.pure,
--     pure, bail, Err.context,
--     resOf, Err.mk
--   ]
--   rfl



@[simp]
abbrev ErrState.divAddDiv? (a b c d : Nat) : ErrStateM (Option Nat) :=
  do
    let d₁ ←
      div? a b
      |>.withContext
        lazy_s!"cannot compute `{a}/{b}`"
      |> ErrStateT.unwrap?

    let d₂ ←
      div? c d
      |>.withContext
        lazy_s!"cannot compute `{c}/{d}"
      |> ErrStateT.unwrap?

    ErrStateT.withContext
      lazy_s!"failed to compute `{a}/{b} + {c}/{d}"

    if let (some d₁, some d₂) := (d₁, d₂)
    then
      d₁ + d₂ |> some |> pure
    else
      pure none

#eval ErrState.divAddDiv? 3 0 7 0 |>.run default |>.2
