import Cat.Setoid



/-! # Basic categories with setoid morphisms as arrows -/

namespace Cat



/-- A simple category, basis for categories with families. -/
structure Fam.Cat where
  /-- Type of the objects of the category. -/
  Obj : Sort o

  /-- This returns a `Setoid.Erased` to allow dependent, arbitrary carriers. -/
  Hom
  : Obj → Obj → Setoid


  /-- Type-level arrow composition.

  **NB:** `|dom ⇛ cod|` coerces to `|dom| → |cod|`. This is why we can directly write `compose f g`
  without having to perform conversions all over the place.
  -/
  compose
    {α β γ : Obj}
  : |Hom β γ ⇛ Hom α β ⇛ Hom α γ|

  /-- Arrow composition is associative. -/
  compose_assoc
    {α β γ δ : Obj}
    (f : |Hom γ δ|)
    (g : |Hom β γ|)
    (h : |Hom α β|)
  : compose f (compose g h) ≈ compose (compose f g) h


  /-- Identity arrows. -/
  id
    {α : Obj}
  : |Hom α α|

  /-- `id` is a left-identity for `compose`. -/
  id_compose
    (f : |Hom α β|)
  : compose id f ≈ f

  /-- `id` is a right-identity for `compose`. -/
  compose_id
    (f : |Hom α β|)
  : compose f id = f



/-- Same as `ℂ.compose` with explicit type parameters. -/
abbrev Fam.Cat.compose'
  (ℂ : Cat)
  (α β γ : ℂ.Obj)
: |Hom ℂ β γ ⇛ Hom ℂ α β ⇛ Hom ℂ α γ| :=
  @Cat.compose ℂ α β γ

-- /-- Value-level arrow composition. -/
-- abbrev Fam.Cat.compose
--   (ℂ : Cat)
--   {α β γ : ℂ.Obj}
-- : |ℂ.Hom β γ| → |ℂ.Hom α β| → |ℂ.Hom α γ| :=
--   ⟦@Cat.kompose ℂ⟧

theorem Fam.Cat.compose_congr_left
  (ℂ : Cat)
  {α β γ : ℂ.Obj}
  (f f' : |ℂ.Hom β γ|)
  (g : |ℂ.Hom α β|)
: f ≈ f' → ℂ.compose f g ≈ ℂ.compose f' g :=
  let k :=
    ℂ.compose' α β γ
  by
    intro h_f
    apply k.proper h_f

theorem Fam.Cat.compose_congr_right
  (ℂ : Cat)
  {α β γ : ℂ.Obj}
  (f : |ℂ.Hom β γ|)
  (g g' : |ℂ.Hom α β|)
: g ≈ g' → ℂ.compose f g ≈ ℂ.compose f g' :=
  let k :=
    ℂ.compose' α β γ f
  by
    intro h_g
    apply k.proper h_g
