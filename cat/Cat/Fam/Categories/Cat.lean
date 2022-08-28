import Cat.Fam.Functor



/-! # The category of categories -/

namespace Cat



/-- `Func.comp` as a `Comp` structure. -/
def Fam.Cat.CAT.Comp
: Comp Cat Func.mkSetoid where
  comp :=
    Func.comp
  congr :=
    Func.comp.Congr

/-- Functor composition is associative. -/
def Fam.Cat.CAT.comp_assoc
  {ℂ₁ ℂ₂ ℂ₃ ℂ₄ : Cat}
  (F₃₄ : Func ℂ₃ ℂ₄)
  (F₂₃ : Func ℂ₂ ℂ₃)
  (F₁₂ : Func ℂ₁ ℂ₂)
: F₃₄ ⊙ (F₂₃ ⊙ F₁₂) ≈ (F₃₄ ⊙ F₂₃) ⊙ F₁₂ :=
  by
    intro α β f
    simp [Func.fmap, Func.comp]
    apply Hom.Equiv.refl



variable
  {ℂ : Cat}

/-- Identity over category objects. -/
@[simp]
abbrev Fam.Cat.CAT.idObj
  (α : ℂ.Obj)
: ℂ.Obj :=
  α

/-- Identity over category arrows. -/
@[simp]
abbrev Fam.Cat.CAT.idMap
  {α β : ℂ.Obj}
: (ℂ.Hom α β) ⇒ (ℂ.Hom α β) :=
  Morph.id

/-- Functor identity respects composition law. -/
theorem Fam.Cat.CAT.comp_law
  {α β γ : ℂ.Obj}
  (f : β ↠ γ)
  (g : α ↠ β)
: Func.law.comp idObj idMap f g :=
  by
    simp [Morph.id]
    apply Morph.equiv.refl

/-- Functor identity respects identity law. -/
theorem Fam.Cat.CAT.id_law
  {α : ℂ.Obj}
: Func.law.id' idObj idMap α :=
  by
    simp [Morph.id]
    apply (ℂ.Hom α α).refl



/-- Functor identity. -/
def Fam.Cat.CAT.Id
: Func ℂ ℂ where
  fObj :=
    idObj
  fMap :=
    idMap
  comp_law :=
    comp_law
  id_law :=
    id_law

/-- Functor identity is left-neutral for functor composition. -/
def Fam.Cat.CAT.Id.id_comp
  {ℂ₁ ℂ₂ : Cat}
  (F : Func ℂ₁ ℂ₂)
: Id ⊙ F ≈ F :=
  by
    intro α β f
    simp [Func.fmap, Func.comp, Id, Morph.id]
    apply Hom.Equiv.refl

/-- Functor identity is right-neutral for functor composition. -/
def Fam.Cat.CAT.Id.comp_id
  {ℂ₁ ℂ₂ : Cat}
  (F : Func ℂ₁ ℂ₂)
: F ⊙ Id ≈ F :=
  by
    intro α β f
    simp [Func.fmap, Func.comp, Id, Morph.id]
    apply Hom.Equiv.refl



def Fam.Cat.CAT
: Cat where
  Obj :=
    Cat
  Hom :=
    Func.mkSetoid

  compose :=
    CAT.Comp.toMorph2
  compose_assoc :=
    CAT.comp_assoc

  id :=
    CAT.Id
  id_compose :=
    CAT.Id.id_comp
  compose_id :=
    CAT.Id.comp_id