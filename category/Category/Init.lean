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



--- Category **0** with no objects and no arrows.
def Cat.zero : Cat Empty :=
  by
    apply Cat.mk
    <;> (
      intros
      contradiction
    )



--- Category **1** with one object and its identity arrow.
def Cat.one : Cat Unit where
  Arrow _ _  :=
    Unit
  compose _ _ := ()
  compose_assoc _ _ _ :=
    rfl
  id := ()
  id_compose _ :=
    rfl
  compose_id _ :=
    rfl



--- Empty structure that stores two booleans as type parameters.
---
--- This is going to be the arrow for category `Cat.two`.
structure Cat.two.Arrow (b₁ b₂ : Bool)

--- Category **2** with two objects, two identity arrows, and an arrow from one object to the other.
def Cat.two : Cat Bool where
  Arrow :=
    two.Arrow
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
def Cat.three : Cat three.Object where
  Arrow :=
    three.Arrow
  compose _ _ := {}
  compose_assoc _ _ _ :=
    rfl
  id := {}
  id_compose _ :=
    rfl
  compose_id _ :=
    rfl



--- Dual of a category.
instance Cat.Dual (cat : Cat Object) : Cat Object where
  Arrow dom cod :=
    cat.Arrow cod dom
  
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
