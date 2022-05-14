import Category.Init


/-!
# Category **Poset**

`Poset` is the **Poset** category:
- objects are all the partially-ordered sets, and
- arrows are all the order-preserving functions between objects.
-/



namespace Poset

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



  protected def ProperFn.id {p : outParam All} : ProperFn p p where
    apply := id
    apply_post _ _ := id

  theorem ProperFn.compose_id
    (f : ProperFn s₁ s₂)
    : f.compose ProperFn.id = f
  :=
    rfl

  theorem ProperFn.id_compose
    (f : ProperFn s₁ s₂)
    : ProperFn.id.compose f = f
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

  id :=
    @Poset.ProperFn.id
  compose_id :=
    @Poset.ProperFn.compose_id
  id_compose :=
    @Poset.ProperFn.id_compose
