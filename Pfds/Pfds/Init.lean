import Std



/-- `𝕂`onstant combinator. -/
def 𝕂 : α → β → α :=
  fun a _ => a



/-- Removes duplicates in a list. -/
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


def IO.check! [ToString α] [BEq α] (val exp : α) : IO α := do
  if val != exp then
    IO.throwServerError s!"error on value `{val}`: expected `{exp}`"
  return val


/-! Augmenting `Thunk` with a convenient syntax extension and a `Monad` instance.

Operator `lazy` builds thunks: `lazy t` elaborates to `Thunk.mk (𝕂 t)`.
-/
section thunk

  /-- Builds a `Thunk` (lazily) evaluating to a term. -/
  syntax:max "lazy " term : term

  macro_rules
  | `(lazy $t) => `(Thunk.mk fun _ => $t)

  instance _root_.Thunk.instMonad : Monad Thunk where
    pure := Thunk.pure
    bind := Thunk.bind
    map := Thunk.map

  instance _root_.Thunk.instLawfulMonad : LawfulMonad Thunk where
    map_const := by intros ; rfl
    id_map := by intros ; rfl
    bind_pure_comp := by intros ; rfl
    bind_map := by intros ; rfl
    bind_assoc := by intros ; rfl
    pure_bind := by intros ; rfl
    pure_seq := by intros ; rfl
    seqLeft_eq := by intros ; rfl
    seqRight_eq := by intros ; rfl
end thunk
