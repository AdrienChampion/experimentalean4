import Mathlib

/-!
# Useful helpers

Contains the actual category class `Cat`.
-/



--- A category with objects of type `Object`.
class Cat (Object : Sort o) where
  --- Type of the arrows of the category.
  Arrow :
    Object → Object → Sort a

  --- Arrow composition.
  compose {α β γ} :
    Arrow β γ → Arrow α β → Arrow α γ
  --- Arrow composition is associative.
  compose_assoc (f : Arrow γ δ) (g : Arrow β γ) (h : Arrow α β) :
    compose f (compose g h)
    =
    compose (compose f g) h

  --- Identity, careful not to shadow `id`.
  protected id {α : outParam Object} :
    Arrow α α
  --- `id ∘ f` is `f`.
  id_compose (f : Arrow α β) :
    compose id f = f
  --- `f ∘ id` is `f`.
  compose_id (f : Arrow α β) :
    compose f id = f

--- Nice notation for `Cat.Arrow`, enter `\r=`.
infixr:80 " ⇒ " => Cat.Arrow
--- Usual function composition.
infixr:80 " ∘ " => Cat.compose



--- Category with no objects and no arrows.
def Cat.zero : Cat Empty :=
  by
    apply Cat.mk
    <;> (
      intros
      contradiction
    )



--- Category with one object and its identity arrow.
def Cat.one : Cat Unit where
  Arrow _ _  :=
    Unit
  compose f g :=
    ()
  compose_assoc _ _ _ :=
    rfl
  id :=
    ()
  id_compose _ :=
    rfl
  compose_id _ :=
    rfl
