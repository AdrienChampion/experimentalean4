import Cat.Fam.Functor



/-! # Additional definitions for functors -/

namespace Cat



/-! ## Functors and iso arrows/objects  -/
section iso_proper
  variable
    {ℂ₁ ℂ₂ : Fam.Cat}
    (F : Fam.Cat.Func ℂ₁ ℂ₂)

  theorem Fam.Cat.Func.proper_inv
    {α β : ℂ₁.Obj}
    {f₁ : α ↠ β}
    {f₂ : β ↠ α}
    (h : f₁ ⊚ f₂ ≈ ℂ₁.id)
  : (F.fMap f₁) ⊚ (F.fMap f₂) ≈ F.id :=
    let f₁' :=
      F.fMap f₁
    let f₂' :=
      F.fMap f₂
    let h₁ : f₁' ⊚ f₂' ≈ F.fMap (f₁ ⊚ f₂) :=
      F.comp_law f₁ f₂
      |> Setoid.symm
    let h₂ : f₁' ⊚ f₂' ≈ F.fMap ℂ₁.id :=
      F.fmap_proper h
      |> Setoid.trans h₁
    let h₃ : f₁' ⊚ f₂' ≈ ℂ₂.id :=
      F.id_law' β
      |> Setoid.trans h₂
    h₃

  /-- Functors preserve the *iso* property over arrows. -/
  instance instIsoFuncIso
    {F : Fam.Cat.Func ℂ₁ ℂ₂}
    {α β : ℂ₁.Obj}
    (f : α ↠ β)
    [instIso : Fam.Cat.Iso f]
  : Fam.Cat.Iso (F.fmap f) :=
    let fInv' :=
      F.fmap instIso.inv
    Fam.Cat.Iso.mk
      fInv'
      (F.proper_inv instIso.law_left)
      (F.proper_inv instIso.law_right)
  

  /-- Functors preserve the *iso* property over objects. -/
  instance instIsoObjFuncIsoObj
    {α β : ℂ₁.Obj}
    (h_iso : α ≅ β)
  : F α ≅ F β where
    iso :=
      F.fmap h_iso.iso
    instIso :=
      instIsoFuncIso h_iso.iso

end iso_proper



/-! ## Faithful / full functors -/
section
  variable
    {ℂ₁ ℂ₂ : Fam.Cat}
    (F : Fam.Cat.Func ℂ₁ ℂ₂)

  /-- Proof that a functor is *faithful*, *i.e.* `F f ≈ F g → f ≈ g`. -/
  class Fam.Cat.Func.Faithful
    {ℂ₁ ℂ₂ : Cat}
    (F : Func ℂ₁ ℂ₂)
  where
    /-- Faithfulness law. -/
    law' :
      ∀ {α β : ℂ₁.Obj} (f g : α ↠ β),
        F.fmap f ≈ F.fmap g → f ≈ g

  /-- Same as `Faithful.law'` but `f` and `g` are implicit. -/
  @[simp]
  abbrev Fam.Cat.Func.Faithful.law
    [inst : Faithful F]
    {α β : ℂ₁.Obj}
    {f g : α ↠ β}
  : F.fmap f ≈ F.fmap g → f ≈ g :=
    inst.law' f g

  /-- Faithfulness is closed under functor composition. -/
  instance instFaithfulFuncComp
    (F₂₃ : Fam.Cat.Func ℂ₂ ℂ₃)
    [inst₂₃ : Fam.Cat.Func.Faithful F₂₃]
    (F₁₂ : Fam.Cat.Func ℂ₁ ℂ₂)
    [inst₁₂ : Fam.Cat.Func.Faithful F₁₂]
  : Fam.Cat.Func.Faithful (F₂₃ ⊙ F₁₂) where
    law' {α β} (f g) h :=
      by
        apply inst₁₂.law
        apply inst₂₃.law
        exact h



  /-- Proof that a functor is *full*, *i.e.* any `h : F α ↠ F β` has a preimage by `F.fmap`. -/
  class Fam.Cat.Func.Full
    {ℂ₁ ℂ₂ : Cat}
    (F : Func ℂ₁ ℂ₂)
  where
    /-- Yields the preimage of `h` by `F.fmap`. -/
    preimage
      {α β : ℂ₁.Obj}
      (h : F α ↠ F β)
    : α ↠ β
    /-- Proof that `h` and the image of its preimage are equivalent. -/
    law'
      {α β : ℂ₁.Obj}
      (h : F α ↠ F β)
    : h ≈ F.fmap (preimage h)

  /-- Same as `Full.law'` but `h` is implicit. -/
  @[simp]
  abbrev Fam.Cat.Func.Full.law
    [inst : Full F]
    {α β : ℂ₁.Obj}
    {h : F α ↠ F β}
  : h ≈ F.fmap (inst.preimage h) :=
    inst.law' h

  /-- Fullness is closed under functor composition. -/
  instance instFullFuncComp
    (F₂₃ : Fam.Cat.Func ℂ₂ ℂ₃)
    [inst₂₃ : Fam.Cat.Func.Full F₂₃]
    (F₁₂ : Fam.Cat.Func ℂ₁ ℂ₂)
    [inst₁₂ : Fam.Cat.Func.Full F₁₂]
  : Fam.Cat.Func.Full (F₂₃ ⊙ F₁₂) where
    preimage h :=
      inst₂₃.preimage h
      |> inst₁₂.preimage
    law' g₃ :=
      let g₂ :=
        inst₂₃.preimage g₃
      let g₁ :=
        inst₁₂.preimage g₂
      let h : g₃ ≈ F₂₃.fmap g₂ :=
        inst₂₃.law
      let h' : g₂ ≈ F₁₂.fmap g₁ :=
        inst₁₂.law
      let h : g₃ ≈ F₂₃.fmap (F₁₂.fmap g₁) :=
        F₂₃.fmap_proper h'
        |> Setoid.trans h
      h

end



/-! ## Natural transformations

Natural transformations define a setoid, which is what we're defining here.
-/
section nat_trans

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

end nat_trans
