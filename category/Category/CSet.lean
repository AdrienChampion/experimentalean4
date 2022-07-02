import Category.Init


/-!
# Category **Set**

`CSet` is the **Set** category:
- objects are all the sets, and
- arrows are all the total functions between sets.
-/



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



  protected def Fn.id {s : outParam All} : Fn s s where
    apply a _ := a
    apply_post _ := id

  theorem Fn.compose_id
    (f : Fn s₁ s₂)
    : f.compose Fn.id = f
  :=
    rfl

  theorem Fn.id_compose
    (f : Fn s₁ s₂)
    : Fn.id.compose f = f
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

  id :=
    @CSet.Fn.id
  id_compose :=
    CSet.Fn.id_compose
  compose_id :=
    CSet.Fn.compose_id
