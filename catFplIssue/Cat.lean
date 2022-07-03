/-! # FPL category

From *Basic Category Theory for Computer Scientists* by **Benjamin C. Pierce**, page 7-8.
-/

--- Objects.
inductive O
| int
| real
| bool
| unit
deriving Inhabited, BEq, Repr

--- Arrows.
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

  -- `unit → bool`
  | tru : Arrow O.unit O.bool
  | fls : Arrow O.unit O.bool
  -- `unit → int`
  | zero : Arrow O.unit O.int
  -- `int → bool`
  | isZero : Arrow O.int O.bool
  -- `int → real`
  | toReal : Arrow O.int O.real
deriving Repr

def Arrow.compose₁ {α β γ : O} :
  Arrow β γ
  → Arrow α β
  → Arrow α γ
| id, g => g
| f, id => f
| comp f₁ f₂, g => comp f₁ (comp f₂ g)
| f, g => comp f g
#print Arrow.compose₁
-- def Arrow.compose₁ : {α β γ : O} → Arrow β γ → Arrow α β → Arrow α γ :=
-- fun {α β γ} x x_1 =>
--   match β, γ, x, x_1 with
--   | β, .(β), Arrow.id, g => g
--   | .(α), γ, f, Arrow.id => f
--   | β, γ, Arrow.comp f₁ f₂, g => Arrow.comp f₁ (Arrow.comp f₂ g)
--   | β, γ, f, g => Arrow.comp f g
#eval Arrow.compose₁ Arrow.unit Arrow.id
-- Arrow.comp (Arrow.unit) (Arrow.id)

def Arrow.compose₂
  : {α β γ : O}
  → Arrow β γ
  → Arrow α β
  → Arrow α γ
| α, β, .(β), id, g => g
| α, .(α), γ, f, id => f
| α, β, γ, comp f₁ f₂, g => comp f₁ (comp f₂ g)
| α, β, γ, f, g => comp f g
#print Arrow.compose₂
-- def Arrow.compose₂ : {α β γ : O} → Arrow β γ → Arrow α β → Arrow α γ :=
-- fun x x_1 x_2 x_3 x_4 =>
--   match x, x_1, x_2, x_3, x_4 with
--   | α, β, .(β), Arrow.id, g => g
--   | α, .(α), γ, f, Arrow.id => f
--   | α, β, γ, Arrow.comp f₁ f₂, g => Arrow.comp f₁ (Arrow.comp f₂ g)
--   | α, β, γ, f, g => Arrow.comp f g
#eval Arrow.compose₂ Arrow.unit Arrow.id
-- Arrow.comp (Arrow.unit) (Arrow.id)

theorem Arrow.id_compose₁
  {α β : O} (f : Arrow α β)
  : Arrow.compose₁ id g = g :=
  by
    simp only [compose₁]

theorem Arrow.compose₁_id
  {α β : O} (f : Arrow α β)
  : @Arrow.compose₁ α α β f id = f :=
  by
    cases f
    <;> simp [compose₁]
    <;> sorry
    
theorem Arrow.id_compose : Arrow.compose₁ id g = g :=
  by
    simp only [compose₁]
theorem Arrow.compose_id : Arrow.compose₁ f id = f :=
  by
    simp only [compose₁]
-- failed to generate equality theorems for `match` expression `Arrow.compose₁.match_1`
-- case unit
-- motive : (β γ : O) → Arrow β γ → Arrow O.unit β → Sort u_1
-- h_1 : (β : O) → (g : Arrow O.unit β) → motive β β id g
-- h_2 : (γ : O) → (f : Arrow O.unit γ) → motive O.unit γ f id
-- h_3 : (β γ β_1 : O) → (f₁ : Arrow β_1 γ) → (f₂ : Arrow β β_1) → (g : Arrow O.unit β) → motive β γ (comp f₁ f₂) g
-- h_4 : (β γ : O) → (f : Arrow β γ) → (g : Arrow O.unit β) → motive β γ f g
-- : O.unit = O.unit → HEq unit id → False
-- ⊢ h_4 O.unit O.unit unit id = h_2 O.unit unit