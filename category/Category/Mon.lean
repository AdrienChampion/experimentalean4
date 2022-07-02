import Category.Init


/-!
# Category **Mon**

`Mon` is the **Mon** category:
- objects are all the monoids, and
- arrows are all the *monoid homomorphisms*.

*Monoid homomorphisms* preserve the neutral element and are proper *w.r.t.* the monoid's
multiplication.
-/



namespace Mon

  structure All where
    Elm : α
    mon : Monoid α

  def All.mul {self : All} (a b : self.Elm) : self.Elm :=
    self.mon.mul a b

  local infixl:70 " * " => All.mul



  structure Homo (m₁ m₂ : All) where
    apply (a₁ : m₁.Elm) : m₂.Elm
    apply_one : apply m₁.mon.one = m₂.mon.one
    apply_proper (a₁ b₁ : m₁.Elm) :
      apply (a₁ * b₁) = apply a₁ * apply b₁

  def Homo.compose
    (g : Homo m₂ m₃)
    (f : Homo m₁ m₂)
    : Homo m₁ m₃
  where
    apply a₁ := g.apply (f.apply a₁)
    apply_one :=
      by
        simp
        rw [f.apply_one, g.apply_one]
    apply_proper a₁ b₁ :=
      by
        simp
        rw [f.apply_proper, g.apply_proper]

  def Homo.compose_assoc
    (h : Homo s₃ s₄)
    (g : Homo s₂ s₃)
    (f : Homo s₁ s₂)
    : h.compose (g.compose f) = (h.compose g).compose f
  :=
    rfl



  protected def Homo.id {s : outParam All} : Homo s s where
    apply := id
    apply_one := rfl
    apply_proper _ _ := rfl

  theorem Homo.compose_id
    (f : Homo m₁ m₂)
    : f.compose Homo.id = f
  :=
    rfl

  theorem Homo.id_compose
    (f : Homo m₁ m₂)
    : Homo.id.compose f = f
  :=
    rfl

end Mon



instance Cat.Mon : Cat Mon.All where
  Arrow :=
    Mon.Homo

  compose :=
    Mon.Homo.compose
  compose_assoc :=
    Mon.Homo.compose_assoc

  id :=
    @Mon.Homo.id
  id_compose :=
    Mon.Homo.id_compose
  compose_id :=
    Mon.Homo.compose_id



structure Cat.SingleMon.Arrow (Elm : Sort e) where
  val : Elm

instance Cat.SingleMon [mon : Monoid Elm] : Cat Unit where
  Arrow _ _ :=
    SingleMon.Arrow Elm

  compose f g :=
    ⟨f.val * g.val⟩
  compose_assoc f g h :=
    by simp [mon.mul_assoc f.val g.val h.val]

  id := ⟨1⟩
  id_compose :=
    by simp at *
  compose_id :=
    by simp at *

