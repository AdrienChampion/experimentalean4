import Mathlib



/-!
# Useful helpers

Contains the actual category class `Cat`.
-/



/-! ## Constant combinator -/

abbrev 𝕂
  {α : Sort u}
  {β : Sort v}
  (val : β)
: α → β :=
  fun _ => val



/-! ## Defining categories -/



--- A category with objects of type `Object`.
@[reducible]
class Cat
  (Object : Sort o)
  (OSem : outParam (Object → Sort osem))
  (Arrow : Object → Object → Sort a)
  (ASem : outParam (Object → Object → Sort asem))
where
  --- Arrow concretization.
  aConcrete :
    (A : Arrow α β) → ASem α β

  --- Arrow composition.
  compose {α β γ} :
    Arrow β γ → Arrow α β → Arrow α γ
  --- Arrow composition is associative.
  compose_assoc {α β γ δ} (f : Arrow γ δ) (g : Arrow β γ) (h : Arrow α β) :
    aConcrete (compose f (compose g h))
    =
    aConcrete (compose (compose f g) h)

  --- Identity, careful not to shadow `id`.
  protected id {α : outParam Object} :
    Arrow α α
  --- `id ∘ f` is `f`.
  id_compose (f : Arrow α β) :
    aConcrete (compose id f) = aConcrete f
  --- `f ∘ id` is `f`.
  compose_id (f : Arrow α β) :
    aConcrete (compose f id) = aConcrete f


class Cat.Abstract
  (Object : Sort o)
  (Arrow : Object → Object → Sort a)
extends
  Cat Object (𝕂 Object) Arrow Arrow
where
  aConcrete a := a



--- Nice notation for `Cat.Arrow`, enter `\r=`.
infixr:80 " ⇒ " => Cat.Arrow
--- Usual function composition.
infixr:80 " ∘c " => Cat.compose



--- Category **0** with no objects and no arrows.
def Cat.zero : Cat.Abstract Empty (fun _ _ => Unit) where
  id :=
    by intros ; contradiction
  compose :=
    by intros ; contradiction
  compose_assoc :=
    by intros ; contradiction
  id_compose :=
    by intros ; contradiction
  compose_id :=
    by intros ; contradiction



--- Category **1** with one object and its identity arrow.
def Cat.one : Cat.Abstract Unit (fun _ _ => Unit) where
  compose _ _ :=
    ()
  compose_assoc _ _ _ :=
    rfl
  id :=
    ()
  id_compose _ :=
    rfl
  compose_id _ :=
    rfl



--- Empty structure that stores two booleans as type parameters.
---
--- This is going to be the arrow for category `Cat.two`.
@[reducible]
structure Cat.two.Arrow (b₁ b₂ : Bool)

--- Category **2** with two objects, two identity arrows, and an arrow from one object to the other.
def Cat.two : Cat.Abstract Bool two.Arrow where
  compose _ _ := {}
  compose_assoc _ _ _ :=
    rfl
  id := {}
  id_compose _ :=
    rfl
  compose_id _ :=
    rfl



--- Objects of the category **3**.
inductive Cat.three.Object
| A
| B
| C

--- Arrows of the category **3**.
structure Cat.three.Arrow (o₁ o₂ : Cat.three.Object)

--- Category **3** with three objects `A`, `B` and `C`.
---
--- Besides the three identity arrows, we have `A → B`, `B → C`, and `C → A`.
def Cat.three : Cat.Abstract three.Object three.Arrow where
  compose _ _ := {}
  compose_assoc _ _ _ :=
    rfl
  id := {}
  id_compose _ :=
    rfl
  compose_id _ :=
    rfl



--- Dual of a category.
instance Cat.Abstract.dual
  (cat : Cat.Abstract Object Arrow)
: Cat.Abstract Object (fun α β => Arrow β α) where
  compose f g :=
    cat.compose g f
  compose_assoc f g h :=
    by
      simp
      rw [cat.compose_assoc h g f]

  id := cat.id
  id_compose :=
    cat.compose_id
  compose_id :=
    cat.id_compose

--- Applying `Dual` two times yields the original.
theorem Cat.Abstract.dual_dual
  (cat : Cat.Abstract Object Arrow)
: cat.dual.dual = cat :=
  rfl



instance Cat.Prod
  (cat₁ : Cat O₁ OSem₁ A₁ ASem₁)
  (cat₂ : Cat O₂ OSem₂ A₂ ASem₂)
: Cat
  (PProd O₁ O₂)
  (fun ⟨o₁, o₂⟩ => OSem₁ o₁ × OSem₂ o₂)
  (fun ⟨α₁, α₂⟩ ⟨β₁, β₂⟩ => PProd (A₁ α₁ β₁) (A₂ α₂ β₂))
  (fun ⟨α₁, α₂⟩ ⟨β₁, β₂⟩ => PProd (ASem₁ α₁ β₁) (ASem₂ α₂ β₂))
where
  aConcrete a :=
    ⟨cat₁.aConcrete a.1, cat₂.aConcrete a.2⟩
  compose f g :=
    ⟨cat₁.compose f.1 g.1, cat₂.compose f.2 g.2⟩
  compose_assoc {α β γ δ} f g h :=
    let res : _ ∧ _ :=
      ⟨cat₁.compose_assoc f.1 g.1 h.1, cat₂.compose_assoc f.2 g.2 h.2⟩
    by
      simp [res]
  id :=
    ⟨cat₁.id, cat₂.id⟩
  id_compose f :=
    let res : _ ∧ _ :=
      ⟨cat₁.id_compose f.1, cat₂.id_compose f.2⟩
    by
      simp [res]
  compose_id f :=
    let res : _ ∧ _ :=
      ⟨cat₁.compose_id f.1, cat₂.compose_id f.2⟩
    by
      simp [res]
