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

  /-- Left congruence. -/
  congr_left
    {α β γ : Obj}
    {f f' : |Hom β γ|}
    (g : |Hom α β|)
  : f ≈ f' → comp f g ≈ comp f' g

  /-- Right congruence. -/
  congr_right
    {α β γ : Obj}
    (f : |Hom β γ|)
    {g g' : |Hom α β|}
  : g ≈ g' → comp f g ≈ comp f g'



/-- Congruence on both sides. -/
def Fam.Comp.congr
  (self : Fam.Comp Obj Hom)
  {α β γ : Obj}
  (f f' : |Hom β γ|)
  (g g' : |Hom α β|)
: f ≈ f' → g ≈ g' → self.comp f g ≈ self.comp f' g' :=
  fun h_f h_g =>
    let left :=
      self.congr_left g h_f
    let right :=
      self.congr_right f' h_g
    Hom α γ
    |>.trans left right



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
    c.congr_right f

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
  congr_left :=
    Cat.compose.congr_left
  congr_right :=
    Cat.compose.congr_right

@[simp]
def Fam.Cat.toComp :=
  @Fam.Comp.ofCat
