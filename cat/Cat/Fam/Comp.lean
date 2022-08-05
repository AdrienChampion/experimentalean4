import Cat.Fam.Cat



/-! # Generalizes composition as a congruence-laws-compliant binary function -/

namespace Cat



/-- A composition function with its congruence lemmas. -/
structure Fam.Comp.{u, u'}
  (Obj : outParam (Sort u))
  (Hom : outParam (Obj → Obj → Setoid.{u'}))
: Type (max u u') :=
  /-- Binary composition function. -/
  comp
    {α β γ : Obj}
  : |Hom β γ| → |Hom α β| → |Hom α γ|

  /-- Congruence instance -/
  congr
    {α β γ : Obj}
  : Congr |Hom β γ| |Hom α β| |Hom α γ| comp



/-- Turns a `Comp` into the morphism of *left*-composition *by* `f` (`λ g => f ∘ g`). -/
@[simp]
def Fam.Comp.toMorph
  (c : Comp Obj Hom)
  {α β γ : Obj}
  (f : |Hom β γ|)
: |Hom α β ⇛ Hom α γ| where
  map :=
    c.comp f
  proper :=
    c.congr.right f

/-- Turns a `Comp` into a composition morphism (as a setoid). -/
@[simp]
def Fam.Comp.toMorph2
  (c : Comp Obj Hom)
  {α β γ : Obj}
: |Hom β γ ⇛ Hom α β ⇛ Hom α γ| where
  map f :=
    c.toMorph f
  proper {f f'} h_f :=
    by
      simp only
      intro g
      apply c.congr.left g h_f

/-- Same as `Fam.Comp.toMorph`. -/
@[simp]
abbrev Morph.ofComp :=
  @Fam.Comp.toMorph

/-- Same as `Fam.Comp.toMorph2`. -/
@[simp]
abbrev Morph.ofComp2 :=
  @Fam.Comp.toMorph2

/-- Composition over morphisms defines a `Fam.Comp`. -/
def Morph.compose.Comp
: Fam.Comp Setoid Morph.mkSetoid where
  comp f g :=
    f ∘M g
  congr :=
    Morph.compose.congr



/-- Extracts the composition operation of a category. -/
@[simp]
def Fam.Comp.ofCat
  (ℂ : Cat)
: Comp ℂ.Obj ℂ.Hom where
  comp :=
    ℂ.kompose
  congr :=
    ℂ.congr

/-- Same as `Fam.Comp.ofCat`. -/
@[simp]
abbrev Fam.Cat.toComp :=
  @Fam.Comp.ofCat



/-- Builds a category from a `Fam.Comp`. -/
def Fam.Comp.toCat
  (self : Comp Obj Hom)
  (comp_assoc :
    {α β γ δ : Obj}
    → (f : |Hom γ δ|)
    → (g : |Hom β γ|)
    → (h : |Hom α β|)
    → self.comp f (self.comp g h) ≈ self.comp (self.comp f g) h
  )
  (idty :
    {α : Obj} → |Hom α α|
  )
  (idty_comp :
    {α β : Obj}
    → (f : |Hom α β|)
    → self.comp idty f ≈ f
  )
  (comp_idty :
    {α β : Obj}
    → (f : |Hom α β|)
    → self.comp f idty ≈ f
  )
: Cat where
  Obj :=
    Obj
  Hom :=
    Hom
  compose :=
    self.toMorph2
  compose_assoc :=
    comp_assoc
  id :=
    idty
  id_compose :=
    idty_comp
  compose_id :=
    comp_idty

/-- Same as `Fam.Comp.toCat`. -/
abbrev Fam.Cat.ofComp :=
  @Fam.Comp.toCat

