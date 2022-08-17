/-! # Useful helpers -/

namespace Cat


/-- `𝕂`onstant combinator: `𝕂 val arg` returns `val` for all `arg`s. -/
abbrev 𝕂
  {α : Sort u}
  {β : Sort v}
  (val : β)
: α → β :=
  fun _ => val



/-! ## Congruence helpers -/
section congr

  class Congr
    (α : Sort u_α)
    (β : Sort u_β)
    (γ : Sort u_γ)
    [instα : HasEquiv α]
    [instβ : HasEquiv β]
    [instγ : HasEquiv γ]
    -- [Trans instγ.Equiv instγ.Equiv instγ.Equiv]
    (compose : α → β → γ)
  where
    left
      {f f' : α}
      (g : β)
    : f ≈ f'
    → compose f g ≈ compose f' g

    right
      (f : α)
      {g g' : β}
    : g ≈ g'
    → compose f g ≈ compose f g'

  theorem Congr.both
    [instα : HasEquiv α]
    [instβ : HasEquiv β]
    [instγ : HasEquiv γ]
    [Trans instγ.Equiv instγ.Equiv instγ.Equiv]
    [C : Congr α β γ compose]
  : {f f' : α}
  → {g g' : β}
  → f ≈ f'
  → g ≈ g'
  → compose f g ≈ compose f' g'
  :=
    fun {_f f' g _g'} h_f h_g =>
      let lft :=
        C.left g h_f
      let rgt :=
        C.right f' h_g
      trans lft rgt
end congr

