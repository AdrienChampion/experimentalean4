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
  --- Arrow composition.
  compose {α β γ} :
    Arrow β γ → Arrow α β → Arrow α γ

  --- Arrow concretization.
  aConcrete :
    (A : Arrow α β) → ASem α β

  -- aConcrete_distributive
  --   {α β γ}
  --   (f : Arrow β γ)
  --   (g : Arrow α β)
  -- : aConcrete (compose f g) = compose (aConcrete f) (aConcrete g)

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



namespace Cat.UpArrow
  universe
    o osem
    a asem

  variable

    {Object : Sort o}
    {ASem : Object → Object → Sort asem}

    (A : Object → Object → Sort a)



  inductive Obj
    (A : Object → Object → Sort a)
  : Sort (max 1 o a)
    | mk : A α β → Obj A

  def Obj.dom : Obj A → Object
    | @Obj.mk _ _ α _β _ =>
      α
  def Obj.cod : Obj A → Object
    | @Obj.mk _ _ _α β _ =>
      β
  def Obj.get : Obj A → ((α : Object) ×' (β : Object) ×' A α β)
    | @Obj.mk _ _ α β a =>
      ⟨α, β, a⟩
  def Obj.getFun : (self : Obj A) → A self.dom self.cod
    | @Obj.mk _ _ _α _β a =>
      a

  def Obj.Concrete
    (ASem : Object → Object → Sort asem)
    (self : Obj A)
  : Sort asem :=
    ASem self.dom self.cod



  variable
    {OSem : Object → Sort osem}
    (cat : Cat Object OSem A ASem)

  structure Arrow
    (α β : Obj A)
  : Sort (max 1 o a)
  where
    a : A α.dom β.dom
    b : A α.cod β.cod
    legal :
      let f :=
        α.getFun
      let f' :=
        β.getFun
      cat.compose f' a
      =
      cat.compose b f

  def Arrow.Concrete
    (ASem : Object → Object → Sort asem)
    (α β : Obj A)
  : Sort asem :=
    ASem α.dom β.cod

  def Arrow.concrete
    (self : Arrow A (cat := cat) α β)
  : ASem α.dom β.cod :=
    let a :=
      self.a (cat := cat)
    let f' :=
      β.getFun
    cat.compose f' a
    |> cat.aConcrete

  def Arrow.compose
    {α β γ}
    (f : Arrow A cat β γ)
    (g : Arrow A cat α β)
  : Arrow A cat α γ where
    a :=
      cat.compose f.a g.a
    b :=
      cat.compose f.b g.b
    legal :=
      let legal_f := f.legal
      let legal_g := g.legal
      by
        simp at legal_f
        simp at legal_g
        simp
        sorry
end Cat.UpArrow


/-- Given `cat`, builds `cat⟶` (upperscript arrow, dunno how to unicode it). -/
instance Cat.UpArrow
  [cat : Cat O OSem A ASem]
: Cat
  (UpArrow.Obj A)
  (UpArrow.Obj.Concrete A ASem)
  (UpArrow.Arrow A cat)
  (UpArrow.Arrow.Concrete A ASem)
where
  aConcrete :=
    UpArrow.Arrow.concrete A cat

  compose :=
    by sorry
  compose_assoc :=
    by sorry

  id :=
    by sorry
  id_compose :=
    by sorry
  compose_id :=
    by sorry
