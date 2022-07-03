import Category.Init


/-!
# Category **FPL**

`Fpl` is the **FPL** category:
- objects are all `int`, `real`, `bool` and `unit`, and
- arrows are the following operations:
  - identity on all four objects
  - `isZero : int → bool`
  - `not : bool → bool`
  - `succᵢ : int → int`
  - `succᵣ : real → real`
  - `toReal : int → real`
  - `zero : unit → int`
  - `true : unit → Bool`
  - `false : unit → Bool`
  - `unit : unit → unit`
-/



namespace Fpl

  inductive O
  | int
  | real
  | bool
  | unit
  deriving Inhabited, BEq

  inductive Arrow : (_dom _cod : O) → Type
    -- identity
    | id : {α : O} → Arrow α α

    -- `α → α` arrows
    | unit : Arrow O.unit O.unit
    | not : Arrow O.bool O.bool
    | succᵢ : Arrow O.int O.int
    | succᵣ : Arrow O.real O.real

    -- plain composition, don't create this directly, use `Arrow.compose` instead
    | comp {α β γ} : Arrow β γ → Arrow α β → Arrow α γ

    -- `int → bool`
    | isZero : Arrow O.int O.bool
    -- `unit → bool`
    | tru : Arrow O.unit O.bool
    | fls : Arrow O.unit O.bool
    -- `unit → int`
    | zero : Arrow O.unit O.int
    -- `int → real`
    | toReal : Arrow O.int O.real

  def Arrow.compose -- {α β γ : O}
    -- (f : Arrow β γ)
    -- (g : Arrow α β)
    -- : Arrow α γ
    : {α β γ : O} → Arrow β γ → Arrow α β → Arrow α γ
  -- :=
    -- match (f, g) with
    -- -- noops
    -- | (_, unit) => f
    -- | (id, _) => g
    -- | (_, id) => f
    -- -- compositions yielding existing arrows
    -- | (not, not) => @id O.bool
    -- | (not, tru) => fls
    -- | (not, fls) => tru
    -- | (isZero, zero) => tru
    -- -- plain compositions, exhaustivity check timeouts
    -- | (succᵢ, succᵢ) => comp succᵢ succᵢ
    -- | (succᵣ, succᵣ) => comp succᵣ succᵣ
    -- | (isZero, succᵢ) => comp isZero succᵢ
    -- | (not, isZero) => comp not isZero
    -- | (succᵢ, zero) => comp succᵢ zero
    -- | (toReal, zero) => comp toReal zero
    -- | (toReal, succᵢ) => comp toReal succᵢ
    -- | (succᵣ, toReal) => comp succᵣ toReal
    -- -- composition of compositions
    -- | (comp not isZero, zero) => fls
    -- | (comp f₁ f₂, g) => comp (comp f₁ f₂) g
    -- | (f, comp g₁ g₂) => comp f (comp g₁ g₂)

    | α, β, .(β), @id .(β), g => g
    | α, .(α), γ, f, @id .(α) => f
    | α, β, γ, comp f₁ f₂, g => comp f₁ (comp f₂ g)
    | α, β, γ, f, g => comp f g

  @[simp]
  theorem Arrow.id_compose (g : Arrow α β) : Arrow.compose id g = g :=
    by
      simp only [compose]
  @[simp]
  theorem Arrow.compose_id (f : Arrow α β) : Arrow.compose f id = f :=
    by
      -- simp only [compose]
      sorry

  theorem Arrow.compose_assoc {α β γ δ : O}
    (f : Arrow γ δ) (g : Arrow β γ) (h : Arrow α β)
    : Arrow.compose f (Arrow.compose g h)
    = Arrow.compose (Arrow.compose f g) h
  := by
    -- unfold compose
    -- <;> cases f
    -- <;> simp
    -- <;>
      sorry
end Fpl



def Cat.Fpl : Cat Fpl.O where
  Arrow :=
    Fpl.Arrow

  compose :=
    Fpl.Arrow.compose
  compose_assoc :=
    Fpl.Arrow.compose_assoc

  id :=
    Fpl.Arrow.id
  id_compose :=
    Fpl.Arrow.id_compose
  compose_id :=
    Fpl.Arrow.compose_id
