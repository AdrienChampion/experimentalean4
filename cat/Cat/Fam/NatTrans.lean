import Cat.Fam.FunctorDefs



/-! ## Natural transformations

Natural transformations define a setoid, which is what we're defining here.
-/

namespace Cat


/-- A natural transformation -/
structure Fam.Cat.NatTrans
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
abbrev Fam.Cat.NatTrans.equiv
  {F F' : Func ℂ₁ ℂ₂}
  (T T' : NatTrans F F')
: Prop :=
  ∀ (α : ℂ₁.Obj), T.trans α ≈ T'.trans α

/-- Gives access to `≈` notation (`\~~`). -/
instance instHasEquivNatTrans
  {F F' : Fam.Cat.Func ℂ₁ ℂ₂}
: HasEquiv (Fam.Cat.NatTrans F F') where
  Equiv T T' := T.equiv T'

/-- Natural transformation equivalence is reflexive. -/
theorem Fam.Cat.NatTrans.equiv.refl
  (T : NatTrans F F')
: T ≈ T :=
  by
    intro
    apply Setoid.refl

/-- Natural transformation equivalence is symmetric. -/
theorem Fam.Cat.NatTrans.equiv.symm
  {T T' : NatTrans F F'}
: T ≈ T' → T' ≈ T :=
  by
    intro h α
    apply Setoid.symm
    exact h α

/-- Natural transformation equivalence is transitive. -/
theorem Fam.Cat.NatTrans.equiv.trans
  {T T' T'' : NatTrans F F'}
: T ≈ T' → T' ≈ T'' → T ≈ T'' :=
  by
    intro h' h'' α
    apply Setoid.trans (h' α)
    exact h'' α

/-- Natural transformation equivalence is an actual equivalence. -/
def Fam.Cat.NatTrans.equiv.iseqv
  {F F' : Func ℂ₁ ℂ₂}
: @Equivalence (NatTrans F F') NatTrans.equiv :=
  ⟨refl, symm, trans⟩



/-- Natural transformations define a setoid in the Lean sense. -/
instance instZetoidNatTrans
  {F F' : Fam.Cat.Func ℂ₁ ℂ₂}
: Zetoid (Fam.Cat.NatTrans F F') where
  r :=
    Fam.Cat.NatTrans.equiv
  iseqv :=
    Fam.Cat.NatTrans.equiv.iseqv

/-- Equivalence over natural transformations is transitive. -/
instance instTransNatTransEquiv
  {F F' : Fam.Cat.Func ℂ₁ ℂ₂}
: Trans
  (Fam.Cat.NatTrans.equiv (F := F) (F' := F'))
  Fam.Cat.NatTrans.equiv
  Fam.Cat.NatTrans.equiv
:=
  ⟨Fam.Cat.NatTrans.equiv.trans⟩

/-- Equivalence over natural transformations is transitive. -/
instance instTransNatTransHasEquiv
  {F F' : Fam.Cat.Func ℂ₁ ℂ₂}
: Trans
  (instHasEquivNatTrans (F := F) (F' := F')).Equiv
  instHasEquivNatTrans.Equiv
  instHasEquivNatTrans.Equiv
:=
  instTransNatTransEquiv




/-- Setoid defined by natural transformations. -/
def Fam.Cat.NatTrans.toSetoid
  (F F' : Func ℂ₁ ℂ₂)
: Setoid :=
  ⟨NatTrans F F', instZetoidNatTrans⟩



section yoneda_map
  variable
    {ℂ : Cat.Fam.Cat}
    {α β γ : ℂ.Obj}

  /-- Composes `f` with `g`. -/
  def Fam.Cat.NatTrans.yoneMap.arrow
    (f : α ↠ β)
    (g : β ↠ γ)
  : α ↠ γ :=
    g ⊚ f

  /-- `arrow` is proper for `≈`. -/
  theorem Fam.Cat.NatTrans.yoneMap.arrow.proper
    (f : α ↠ β)
    {g g' : β ↠ γ}
  : g ≈ g' → arrow f g ≈ arrow f g' :=
    by
      intro h
      apply ℂ.congr.left
      exact h

  /-- `Morph` defined by `arrow f` -/
  def Fam.Cat.NatTrans.yoneMap
    (f : α ↠ β)
    (γ : ℂ.Obj)
  : (ℂ.Hom β γ) ⇒ (ℂ.Hom α γ) where
    map g :=
      yoneMap.arrow f g
    proper :=
      yoneMap.arrow.proper f



  /-- `yoneMap` verifies the natural transformation law. -/
  theorem Fam.Cat.NatTrans.yoneMap.natTransLaw
    (f : α ↠ β)
    {α' β' : ℂ.Obj}
    (g : α' ↠ β')
  : (yoneMap f β') ⊚ (Func.FunSET β |>.fmap g)
  ≈ (Func.FunSET α |>.fmap g) ⊚ (yoneMap f α')
  :=
    by
      intro a
      simp [yoneMap, arrow, Func.fmap, Func.FunSET, kompose, compose', Morph.app2]
      simp [SET, Comp.toCat, Morph.compose.Comp, Morph.compose]

  /-- Yoneda map `Morph` is a natural transformation. -/
  def Fam.Cat.NatTrans.yoneNatTrans
    {ℂ : Cat}
    {α β : ℂ.Obj}
    (f : α ↠ β)
  : NatTrans (Func.FunSET β) (Func.FunSET α) where
    trans γ :=
      yoneMap f γ
    law g :=
      yoneMap.natTransLaw f g

end yoneda_map



/-! ## Natural transformation composition -/
section comp
  variable
    {ℂ₁ ℂ₂ : Fam.Cat}
    {F G H : Fam.Cat.Func ℂ₁ ℂ₂}
    (T : Fam.Cat.NatTrans G H)
    (T' : Fam.Cat.NatTrans F G)

  /-- Natural transformation (vertical) composition `∘v`. -/
  @[simp]
  abbrev Fam.Cat.NatTrans.comp.raw
    (α : ℂ₁.Obj)
  : F α ↠ H α :=
    (T.trans α) ⊚ (T'.trans α)

  def Fam.Cat.NatTrans.comp
  : NatTrans F H where
    trans :=
      comp.raw T T'
    law {α β} f :=
      by
        simp [comp.raw]
        calc
          (trans T β ⊚ trans T' β) ⊚ Func.fmap F f
          ≈ trans T β ⊚ trans T' β ⊚ Func.fmap F f
          :=
            by
              apply Setoid.symm
              apply ℂ₂.compose_assoc
          _
          ≈ trans T β ⊚ Func.fmap G f ⊚ trans T' α
          :=
            T'.law f
            |> ℂ₂.congr.right _
          _
          ≈ (trans T β ⊚ Func.fmap G f) ⊚ trans T' α
          :=
            ℂ₂.compose_assoc _ _ _
          _
          ≈ (Func.fmap H f ⊚ trans T α) ⊚ trans T' α
          :=
            T.law f
            |> ℂ₂.congr.left _
          _
          ≈ Func.fmap H f ⊚ trans T α ⊚ trans T' α
          :=
            by
              apply Setoid.symm
              apply ℂ₂.compose_assoc



  infixr:67 " ∘v " =>
    Fam.Cat.NatTrans.comp.toNatTrans



  def Fam.Cat.NatTrans.comp.congr
  : Congr (NatTrans H G) (NatTrans F H) (NatTrans F G) comp where
    left _ h α :=
      ℂ₂.congr.left _ (h α)
    right _ _ _ h α :=
      ℂ₂.congr.right _ (h α)



  def Fam.Cat.NatTrans.Comp
  : Comp (Func ℂ₁ ℂ₂) (NatTrans.toSetoid) where
    comp :=
      NatTrans.comp
    congr :=
      NatTrans.comp.congr

end comp
