

inductive Opt : Type u → Type (u + 1) :=
  | none : Opt α
  | some : α → Opt α
export Opt (none some)

namespace Opt
  def map (f : α → β) : Opt α → Opt β
    | Opt.none => none
    | Opt.some a => f a |> Opt.some
end Opt
