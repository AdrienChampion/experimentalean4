import Mathlib



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



  def Fn.nop {σ : outParam All} : Fn σ σ where
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

#print Cat.compose_assoc
#check @Cat.CSet.Fn.compose_assoc

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


