/-! # Useful helpers -/



/-- `𝕂`onstant combinator: `𝕂 val arg` returns `val` for all `arg`s. -/
abbrev 𝕂
  {α : Sort u}
  {β : Sort v}
  (val : β)
: α → β :=
  fun _ => val
