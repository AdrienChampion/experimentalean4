import Std



/-- `𝕂`onstant combinator. -/
def 𝕂 : α → β → α :=
  fun a _ => a



def List.dedup
  [DecidableEq α]
: List α → List α :=
  aux []
where aux acc
  | [] => acc
  | hd::tl =>
    let acc :=
      if hd ∈ acc then acc else hd::acc
    aux acc tl
