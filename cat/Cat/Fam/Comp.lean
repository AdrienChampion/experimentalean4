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
: Hom α β ⇒ Hom α γ where
  map :=
    c.comp f
  proper :=
    c.congr.right f

@[simp]
def Fam.Comp.toKomp
  (ℂ : Comp Obj Hom)
  {α β γ : Obj}
: |Hom β γ ⇛ Hom α β ⇛ Hom α γ| where
  map :=
    by sorry
  proper :=
    by sorry

@[simp]
def Morph.ofComp :=
  @Fam.Comp.toMorph



/-- Extracts the composition operation of a category. -/
@[simp]
def Fam.Comp.ofCat
  (ℂ : Cat)
: Comp ℂ.Obj ℂ.Hom where
  comp :=
    ℂ.kompose
  congr :=
    ℂ.congr

@[simp]
def Fam.Cat.toComp :=
  @Fam.Comp.ofCat
