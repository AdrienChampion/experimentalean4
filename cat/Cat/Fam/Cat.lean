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


  /-- Type-level arrow composition `f ⊚ g` (`\oo`).

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
  : compose f id ≈ f



/-- Carrier of `ℂ.Hom α β`, `α ↠ β` (`\rr`). -/
abbrev Fam.Cat.hom
  {ℂ : Cat}
  (α β : ℂ.Obj)
:=
  |ℂ.Hom α β|

infixr:min " ↠ " =>
  Fam.Cat.hom



/-- Same as `ℂ.compose` with explicit type parameters. -/
abbrev Fam.Cat.compose'
  (ℂ : Cat)
  (α β γ : ℂ.Obj)
: |ℂ.Hom β γ ⇛ ℂ.Hom α β ⇛ ℂ.Hom α γ| :=
  @Cat.compose ℂ α β γ

/-- Underlying actual composition function (`⊚`, `\oo`). -/
abbrev Fam.Cat.kompose
  {ℂ : Cat}
  {α β γ : ℂ.Obj}
: (β ↠ γ) → (α ↠ β) → (α ↠ γ) :=
  ⟦ℂ.compose'⟧


infixr:100 " ⊚ " =>
  Fam.Cat.kompose



/-! ## Congruence properties over composition -/

instance instCongrCatCompose
  {ℂ : Fam.Cat}
  {α β γ : ℂ.Obj}
: Congr (β ↠ γ) (α ↠ β) (α ↠ γ) ℂ.kompose where
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

def Fam.Cat.congr
  (ℂ : Cat)
:=
  @instCongrCatCompose ℂ
