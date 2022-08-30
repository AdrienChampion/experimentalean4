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
