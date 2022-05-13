import Mathlib

import Category.Init


class Cat (Object : Sort o) where
  Arrow :
    Object → Object → Sort a

  compose {α β γ} :
    Arrow β γ → Arrow α β → Arrow α γ
  compose_assoc (f : Arrow γ δ) (g : Arrow β γ) (h : Arrow α β) :
    compose f (compose g h)
    =
    compose (compose f g) h

  nop (α : Object) :
    Arrow α α
  nop_compose (f : Arrow α β) :
    compose (nop β) f = f
  compose_nop (f : Arrow α β) :
    compose f (nop α) = f

infixr:80 " ⇒ " => Cat.Arrow
infixr:80 " ∘ " => Cat.compose
export Cat (nop)



namespace Cat.CSet

  structure All where
    Elm : α
    set : Set α

  @[simp]
  def All.mem (self : All) (elm : self.Elm) : Prop :=
    elm ∈ self.set

  --- `Membership` would be nice but the dependent nature of `All.mem` prevents it AFAICT.
  infixr:60 " ∋ " => All.mem



  structure Fn (s₁ s₂ : All) where
    apply (a₁ : s₁.Elm) : s₁ ∋ a₁ → s₂.Elm
    apply_post (a₁ : s₁.Elm) (legal₁ : s₁ ∋ a₁) :
      s₂ ∋ apply a₁ legal₁

  def Fn.compose
    (g : Fn s₂ s₃)
    (f : Fn s₁ s₂)
    : Fn s₁ s₃
  where
    apply (a₁ : s₁.Elm) (legal₁ : s₁ ∋ a₁) :=
      let a₂ := f.apply a₁ legal₁
      let legal₂ := f.apply_post a₁ legal₁
      g.apply a₂ legal₂
    apply_post (a₁ : s₁.Elm) (legal₁ : s₁ ∋ a₁) :=
      let a₂ := f.apply a₁ legal₁
      let legal₂ := f.apply_post a₁ legal₁
      g.apply_post a₂ legal₂

  theorem Fn.compose_assoc
    (h : Fn s₃ s₄)
    (g : Fn s₂ s₃)
    (f : Fn s₁ s₂)
    : h.compose (g.compose f) = (h.compose g).compose f
  :=
    rfl



  def Fn.nop {s : outParam All} : Fn s s where
    apply a _ := a
    apply_post a := id

  theorem Fn.compose_nop
    (f : Fn s₁ s₂)
    : f.compose nop = f
  :=
    rfl

  theorem Fn.nop_compose
    (f : Fn s₁ s₂)
    : nop.compose f = f
  :=
    rfl
end Cat.CSet

instance Cat.CSet : Cat CSet.All where
  Arrow :=
    CSet.Fn

  compose :=
    CSet.Fn.compose
  compose_assoc :=
    CSet.Fn.compose_assoc

  nop :=
    @CSet.Fn.nop
  nop_compose :=
    CSet.Fn.nop_compose
  compose_nop :=
    CSet.Fn.compose_nop



namespace Poset

  @[reducible]
  structure All where
    Elm : α
    ord : PartialOrder Elm
  
  def All.le {self : All} (a : self.Elm) (b : self.Elm) : Prop :=
    self.ord.le a b

  local infix:50 " ≤ " => All.le

  structure ProperFn (p₁ p₂ : All) where
    apply : p₁.Elm → p₂.Elm
    apply_post (a₁ b₁ : p₁.Elm) :
      a₁ ≤ b₁ → apply a₁ ≤ apply b₁
  
  def ProperFn.compose
    (g : ProperFn p₂ p₃)
    (f : ProperFn p₁ p₂)
    : ProperFn p₁ p₃
  where
    apply a₁ :=
      f.apply a₁
      |> g.apply
    apply_post a₁ b₁ h₁ :=
      let a₂ := f.apply a₁
      let b₂ := f.apply b₁
      let h₂ := f.apply_post a₁ b₁ h₁
      g.apply_post a₂ b₂ h₂

  theorem ProperFn.compose_assoc
    (h : ProperFn p₃ p₄)
    (g : ProperFn p₂ p₃)
    (f : ProperFn p₁ p₂)
    : h.compose (g.compose f) = (h.compose g).compose f
  :=
    rfl



  def ProperFn.nop {p : outParam All} : ProperFn p p where
    apply := id
    apply_post _ _ := id

  theorem ProperFn.compose_nop
    (f : ProperFn s₁ s₂)
    : f.compose nop = f
  :=
    rfl

  theorem ProperFn.nop_compose
    (f : ProperFn s₁ s₂)
    : nop.compose f = f
  :=
    rfl

end Poset

instance Cat.Poset : Cat Poset.All where
  Arrow :=
    Poset.ProperFn

  compose :=
    Poset.ProperFn.compose
  compose_assoc :=
    Poset.ProperFn.compose_assoc

  nop :=
    @Poset.ProperFn.nop
  compose_nop :=
    @Poset.ProperFn.compose_nop
  nop_compose :=
    @Poset.ProperFn.nop_compose
