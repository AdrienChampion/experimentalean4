import Cat.Setoid



/-! # Basic categories with setoid morphisms as arrows -/

namespace Cat



/-- A simple category, basis for categories with families. -/
structure Fam.Cat where
  /-- Type of the objects of the category. -/
  Obj
  : Sort o

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

/-- Underlying actual composition function. -/
abbrev Fam.Cat.kompose
  (ℂ : Cat)
  {α β γ : ℂ.Obj}
: |ℂ.Hom β γ| → |ℂ.Hom α β| → |ℂ.Hom α γ| :=
  ⟦ℂ.compose'⟧

-- /-- Value-level arrow composition. -/
-- abbrev Fam.Cat.compose
--   (ℂ : Cat)
--   {α β γ : ℂ.Obj}
-- : |ℂ.Hom β γ| → |ℂ.Hom α β| → |ℂ.Hom α γ| :=
--   ⟦@Cat.kompose ℂ⟧



/-! ## Congruence properties over composition -/

instance instCongrCatCompose
  {ℂ : Fam.Cat}
  {α β γ : ℂ.Obj}
: Congr |ℂ.Hom β γ| |ℂ.Hom α β| |ℂ.Hom α γ| ℂ.kompose where
  left {f f'} g :=
    let k :=
      ℂ.compose' α β γ
    by
      intro h_f
      apply k.proper h_f
  right f {g g'} :=
    let k :=
      ℂ.compose' α β γ f
    by
      intro h_g
      apply k.proper h_g

/-- Left-congruence. -/
theorem Fam.Cat.compose.congr_left
  {ℂ : Cat}
  {α β γ : ℂ.Obj}
  {f f' : |ℂ.Hom β γ|}
  (g : |ℂ.Hom α β|)
: f ≈ f' → ℂ.compose f g ≈ ℂ.compose f' g :=
  let k :=
    ℂ.compose' α β γ
  by
    intro h_f
    apply k.proper h_f

/-- Right-congruence. -/
theorem Fam.Cat.compose.congr_right
  {ℂ : Cat}
  {α β γ : ℂ.Obj}
  (f : |ℂ.Hom β γ|)
  {g g' : |ℂ.Hom α β|}
: g ≈ g' → ℂ.compose f g ≈ ℂ.compose f g' :=
  let k :=
    ℂ.compose' α β γ f
  by
    intro h_g
    apply k.proper h_g

/-- Congruence on both sides. -/
theorem Fam.Cat.compose.congr
  {ℂ : Cat}
  {α β γ : ℂ.Obj}
  {f f' : |ℂ.Hom β γ|}
  {g g' : |ℂ.Hom α β|}
: f ≈ f' → g ≈ g' → ℂ.compose f g ≈ ℂ.compose f' g' :=
  fun h_f h_g =>
    let left :=
      congr_left g h_f
    let right :=
      congr_right f' h_g
    -- retrieve target setoid
    ℂ.Hom α γ
    -- use target setoid's transitivity on equivalence
    |>.trans left right



/-! ## `Cat`egory dual -/
section dual
  variable
    {ℂ : Cat}

  /-- Dual arrow. -/
  abbrev Fam.Cat.DualHom
    (α β : ℂ.Obj)
  : Setoid :=
    ℂ.Hom β α

  /-- Dual composition. -/
  abbrev Fam.Cat.dualCompose
    {α β γ : ℂ.Obj}
    (f : |ℂ.DualHom β γ|)
    (g : |ℂ.DualHom α β|)
  : |ℂ.DualHom α γ| :=
    ℂ.compose g f

  theorem Fam.Cat.dualCompose.congr_left
    {α β γ : ℂ.Obj}
    {f f' : |ℂ.DualHom β γ|}
    (g : |ℂ.DualHom α β|)
  : f ≈ f' → ℂ.dualCompose f g ≈ ℂ.dualCompose f' g :=
    by
      simp
      apply Cat.compose.congr_right

  theorem Fam.Cat.dualCompose.congr_right
    {α β γ : ℂ.Obj}
    (f : |ℂ.DualHom β γ|)
    {g g' : |ℂ.DualHom α β|}
  : g ≈ g' → ℂ.dualCompose f g ≈ ℂ.dualCompose f g' :=
    by
      simp
      apply Cat.compose.congr_left

end dual