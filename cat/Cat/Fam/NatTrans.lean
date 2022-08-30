import Cat.Fam.FunctorDefs



/-! ## Natural transformations

Natural transformations define a setoid, which is what we're defining here.
-/

namespace Cat


/-- A natural transformation -/
structure Fam.Cat.Func.NatTrans
  (F F' : Func ℂ₁ ℂ₂)
where
  trans
    (α : ℂ₁.Obj)
  : F α ↠ F' α
  law
    {α β : ℂ₁.Obj}
    (f : α ↠ β)
  : (trans β) ⊚ (F.fmap f)
  ≈ (F'.fmap f) ⊚ (trans α)

/-- Two transformations are equivalent if they map `α` to the same `α'`. -/
abbrev Fam.Cat.Func.NatTrans.equiv
  {F F' : Func ℂ₁ ℂ₂}
  (T T' : NatTrans F F')
: Prop :=
  ∀ (α : ℂ₁.Obj), T.trans α ≈ T'.trans α

/-- Gives access to `≈` notation (`\~~`). -/
instance instHasEquivNatTrans
  {F F' : Fam.Cat.Func ℂ₁ ℂ₂}
: HasEquiv (Fam.Cat.Func.NatTrans F F') where
  Equiv T T' := T.equiv T'

/-- Natural transformation equivalence is reflexive. -/
theorem Fam.Cat.Func.NatTrans.equiv.refl
  (T : NatTrans F F')
: T ≈ T :=
  by
    intro
    apply Setoid.refl

/-- Natural transformation equivalence is symmetric. -/
theorem Fam.Cat.Func.NatTrans.equiv.symm
  {T T' : NatTrans F F'}
: T ≈ T' → T' ≈ T :=
  by
    intro h α
    apply Setoid.symm
    exact h α

/-- Natural transformation equivalence is transitive. -/
theorem Fam.Cat.Func.NatTrans.equiv.trans
  {T T' T'' : NatTrans F F'}
: T ≈ T' → T' ≈ T'' → T ≈ T'' :=
  by
    intro h' h'' α
    apply Setoid.trans (h' α)
    exact h'' α

/-- Natural transformation equivalence is an actual equivalence. -/
def Fam.Cat.Func.NatTrans.equiv.iseqv
  {F F' : Func ℂ₁ ℂ₂}
: @Equivalence (NatTrans F F') NatTrans.equiv :=
  ⟨refl, symm, trans⟩



/-- Natural transformations define a setoid in the Lean sense. -/
instance instZetoidNatTrans
  {F F' : Fam.Cat.Func ℂ₁ ℂ₂}
: Zetoid (Fam.Cat.Func.NatTrans F F') where
  r :=
    Fam.Cat.Func.NatTrans.equiv
  iseqv :=
    Fam.Cat.Func.NatTrans.equiv.iseqv



/-- Setoid defined by natural transformations. -/
def Fam.Cat.Func.NatTrans.toSetoid
  (F F' : Func ℂ₁ ℂ₂)
: Setoid :=
  ⟨NatTrans F F', instZetoidNatTrans⟩



section yoneda_map
  variable
    {ℂ : Cat.Fam.Cat}
    {α β γ : ℂ.Obj}

  /-- Composes `f` with `g`. -/
  def Fam.Cat.Func.NatTrans.yoneMap.arrow
    (f : α ↠ β)
    (g : β ↠ γ)
  : α ↠ γ :=
    g ⊚ f

  /-- `arrow` is proper for `≈`. -/
  theorem Fam.Cat.Func.NatTrans.yoneMap.arrow.proper
    (f : α ↠ β)
    {g g' : β ↠ γ}
  : g ≈ g' → arrow f g ≈ arrow f g' :=
    by
      intro h
      apply ℂ.congr.left
      exact h

  /-- `Morph` defined by `arrow f` -/
  def Fam.Cat.Func.NatTrans.yoneMap
    (f : α ↠ β)
    (γ : ℂ.Obj)
  : (ℂ.Hom β γ) ⇒ (ℂ.Hom α γ) where
    map g :=
      yoneMap.arrow f g
    proper :=
      yoneMap.arrow.proper f



  /-- `yoneMap` verifies the natural transformation law. -/
  theorem Fam.Cat.Func.NatTrans.yoneMap.natTransLaw
    (f : α ↠ β)
    {α' β' : ℂ.Obj}
    (g : α' ↠ β')
  : (yoneMap f β') ⊚ (FunSET β |>.fmap g)
  ≈ (FunSET α |>.fmap g) ⊚ (yoneMap f α')
  :=
    by
      intro a
      simp [yoneMap, arrow, fmap, FunSET, kompose, compose', Morph.app2]
      simp [SET, Comp.toCat, Morph.compose.Comp, Morph.compose]

  /-- Yoneda map `Morph` is a natural transformation. -/
  def Fam.Cat.Func.NatTrans.yoneNatTrans
    {ℂ : Cat}
    {α β : ℂ.Obj}
    (f : α ↠ β)
  : NatTrans (FunSET β) (FunSET α) where
    trans γ :=
      yoneMap f γ
    law g :=
      yoneMap.natTransLaw f g

end yoneda_map
