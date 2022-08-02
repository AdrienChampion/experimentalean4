import Cat.Fam.Dual



/-! # Useful definitions -/

namespace Cat



/-! ## Epimorphisms

A morphism `f : α → β` is *epi* iff for any two morphisms `g₁ g₂ : β → γ`, we have
`g₁∘f = g₂∘f → g₁ = g₂`.
-/
section epi
  variable
    {ℂ : Fam.Cat}
    {α β : ℂ.Obj}

  @[simp]
  abbrev Fam.Cat.Epic.law'
    (ℂ : Cat)
    {α β : ℂ.Obj}
    (f : |ℂ.Hom α β|)
  : Prop :=
    {γ : ℂ.Obj}
    → (g₁ g₂ : |ℂ.Hom β γ|)
    → ℂ.compose g₁ f ≈ ℂ.compose g₂ f
    → g₁ ≈ g₂

  class Fam.Cat.Epic
    (f : |ℂ.Hom α β|)
  where
    law : Epic.law' ℂ f


  /-- `True` iff `f` is epic. -/
  def Fam.Cat.isEpic
    (f : |ℂ.Hom α β|)
    [Epic f]
  : Prop :=
    true
end epi



/-! ## Monomorphisms

A morphism `f : β → γ` is *monic* iff for any two morphisms `g₁ g₂ : α → β`, we have
`f∘g₁ = f∘g₂ → g₁ = g₂`.
-/
section monic
  variable
    {ℂ : Fam.Cat}
    {β γ : ℂ.Obj}

  @[simp]
  abbrev Fam.Cat.Monic.law'
    (ℂ : Fam.Cat)
    {β γ : ℂ.Obj}
    (f : |ℂ.Hom β γ|)
  : Prop :=
    {α : ℂ.Obj}
    → (g₁ g₂ : |ℂ.Hom α β|)
    → ℂ.compose f g₁ ≈ ℂ.compose f g₂
    → g₁ ≈ g₂

  class Fam.Cat.Monic
    (f : |ℂ.Hom α β|)
  : Type where
    law : Monic.law' ℂ f

  /-- `True` iff `f` is monic. -/
  def Fam.Cat.isMonic
    (f : |ℂ.Hom α β|)
    [Monic f]
  : Prop :=
    true
end monic



/-! ## Isomorphisms

A morphism `f : α → β` is *iso* iff there is a morphism `f⁻¹ : β → α` such that `f⁻¹ ∘ f = id' β`
and `f ∘ f⁻¹ = id' α`.
-/
section iso
  variable
    {ℂ : Fam.Cat}
    {α β : ℂ.Obj}

  -- @[simp]
  -- abbrev Fam.Cat.Iso.law'
  --   (f : |ℂ.Hom α β|)
  --   (g : |ℂ.Hom β α|)
  -- : Prop :=
  --   ℂ.compose g f ≈ ℂ.id

  class Fam.Cat.Iso
    (f : |ℂ.Hom α β|)
  where
    inv :
      |ℂ.Hom β α|
    law_left :
      ℂ.compose f inv ≈ ℂ.id
    law_right :
      ℂ.compose inv f ≈ ℂ.id

  abbrev Fam.Cat.isoInv
    (f : |ℂ.Hom α β|)
    [inst : Iso f]
  : |ℂ.Hom β α| :=
    inst.inv

  /-- Turns a `Iso f` into a `Iso inv`. -/
  instance instIsoSelfInv
    (f : |ℂ.Hom α β|)
    [inst : Fam.Cat.Iso f]
  : Fam.Cat.Iso (ℂ.isoInv f) where
    inv :=
      f
    law_left :=
      inst.law_right
    law_right :=
      inst.law_left

  /-- `True` iff `f` is monic. -/
  def Fam.Cat.isIso
    (f : |ℂ.Hom α β|)
    [Iso f]
  : Prop :=
    true
end iso



/-! Isomorphic objects (`≅`, `\~==`).

Two objects `α` and `β` are *isomorphic* if they are connected by an *iso*-arrow.
-/
section iso_obj
  variable
    {ℂ : Fam.Cat}
    {α β : ℂ.Obj}

  /-- Packages the isomorphism. -/
  class Fam.Cat.IsoObj
    (α β : ℂ.Obj)
  where rawMk ::
    iso : |ℂ.Hom α β|
    instIso : Iso iso

  /-- Bring `Iso i.iso` whenever we manipulate `i : IsoObj α β`. -/
  instance instIso_of_IsoObj
    [inst : Fam.Cat.IsoObj α β]
  : Fam.Cat.Iso (inst.iso) :=
    inst.instIso

  abbrev Fam.Cat.IsoObj.mk
    (iso : |ℂ.Hom α β|)
    [instIso : Iso iso]
  : IsoObj α β :=
    ⟨iso, instIso⟩

  /-- `True` iff `α` and `β` are isomorphic. -/
  def Fam.Cat.isIsoObj
    (α β : ℂ.Obj)
    [IsoObj α β]
  : Prop :=
    true

  infix:10 " ≅ " =>
    Fam.Cat.IsoObj
end iso_obj



/-! ## Initial objects

An object `α` is *initial* iff for any `β` there exists a **unique** arrow in `ℂ.Hom α β`.
-/
section initial_obj
  variable
    {ℂ : Fam.Cat}

  class Fam.Cat.Initial
    (α : ℂ.Obj)
  where
    arrow {β : ℂ.Obj} :
      |ℂ.Hom α β|
    unique {β : ℂ.Obj} (f : |ℂ.Hom α β|) :
      arrow ≈ f

  /-- If `α` is initial, then any `α → α` is actually `id`. -/
  theorem Fam.Cat.Initial.equivId
    [instα : Initial α]
    (f : |ℂ.Hom α α|)
  : f ≈ ℂ.id :=
    let h₁ : f ≈ arrow :=
      instα.unique f
      |> Setoid.symm
    let h₂ : arrow ≈ ℂ.id :=
      instα.unique ℂ.id
    Setoid.trans h₁ h₂

  /-- `True` iff `α` is initial. -/
  def Fam.Cat.isInitial
    (α : ℂ.Obj)
    [Initial α]
  : Prop :=
    true
end initial_obj



/-! ## Terminal objects

An object `β` is *terminal* iff for any `α` there existst a **unique** arrow in `ℂ.Hom α β`.
-/
section terminal_obj
  variable
    {ℂ: Fam.Cat}

  class Fam.Cat.Terminal
    (β : ℂ.Obj)
  where
    arrow {α : ℂ.Obj} :
      |ℂ.Hom α β|
    unique {α : ℂ.Obj} (f : |ℂ.Hom α β|) :
      arrow ≈ f

  /-- If `α` is terminal, then any `α → α` is actually `id`. -/
  theorem Fam.Cat.Terminal.equivId
    [instα : Terminal α]
    (f : |ℂ.Hom α α|)
  : f ≈ ℂ.id :=
    let h₁ : f ≈ arrow :=
      instα.unique f
      |> Setoid.symm
    let h₂ : arrow ≈ ℂ.id :=
      instα.unique ℂ.id
    Setoid.trans h₁ h₂

  /-- `True` iff `β` is terminal. -/
  def Fam.Cat.isTerminal
    (β : ℂ.Obj)
    [Terminal β]
  : Prop :=
    true
end terminal_obj