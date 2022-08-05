import Cat.Fam.HomEq



/-! # Dual of a `Cat`egory -/

namespace Cat



variable
  (ℂ : Cat)

/-- Dual arrow. -/
abbrev Fam.Cat.dualHom
  (α β : ℂ.Obj)
: Setoid :=
  ℂ.Hom β α

/-- Dual composition: actual, non-setoid function. -/
abbrev Fam.Cat.dualKompose
  {α β γ : ℂ.Obj}
  (f : |ℂ.dualHom β γ|)
  (g : |ℂ.dualHom α β|)
: |ℂ.dualHom α γ| :=
  ℂ.compose g f

/-- Dual composition is associative. -/
@[simp]
abbrev Fam.Cat.dualKompose_assoc
  {α β γ δ : ℂ.Obj}
  (f : |ℂ.dualHom γ δ|)
  (g : |ℂ.dualHom β γ|)
  (h : |ℂ.dualHom α β|)
: ℂ.dualKompose f (ℂ.dualKompose g h)
≈ ℂ.dualKompose (ℂ.dualKompose f g) h
:=
  -- symmetric of `ℂ.compose_assoc`
  ℂ.compose_assoc h g f
  |> (ℂ.Hom δ α).symm

/-- Dual composition respects congruence laws. -/
@[simp]
abbrev Fam.Cat.dualCongr
  {α β γ : ℂ.Obj}
: Congr |ℂ.dualHom β γ| |ℂ.dualHom α β| |ℂ.dualHom α γ| ℂ.dualKompose where
  left {_f _f'} g h_f :=
    ℂ.congr.right g h_f
  right f {_g _g'} h_g :=
    ℂ.congr.left f h_g

/-- `Comp` structure for dual composition. -/
@[simp]
abbrev Fam.Cat.dualComp
: Comp ℂ.Obj ℂ.dualHom where
  comp :=
    ℂ.dualKompose
  congr :=
    ℂ.dualCongr

/-- Identity of the dual of a category. -/
@[simp]
abbrev Fam.Cat.dualId
  {α : ℂ.Obj}
: |ℂ.dualHom α α| :=
  ℂ.id

/-- Identity of the dual of a category, type-explicit version. -/
@[simp]
abbrev Fam.Cat.dualId'
  (α : ℂ.Obj)
: |ℂ.dualHom α α| :=
  ℂ.id

/-- Left-composition by `dualId` is identity. -/
@[simp]
abbrev Fam.Cat.id_dualKompose
  {α β : ℂ.Obj}
  (f : |ℂ.dualHom α β|)
: ℂ.dualKompose ℂ.dualId f ≈ f :=
  ℂ.compose_id f

/-- Right-composition by `dualId` is identity. -/
@[simp]
abbrev Fam.Cat.dualKompose_id
  {α β : ℂ.Obj}
  (f : |ℂ.dualHom α β|)
: ℂ.dualKompose f ℂ.dualId ≈ f :=
  ℂ.id_compose f

/-- Dual of a category `ℂᵒᵖ` (`\op`). -/
def Fam.Cat.Dual : Cat :=
  ℂ.dualComp.toCat
    ℂ.dualKompose_assoc
    ℂ.dualId
    ℂ.id_dualKompose
    ℂ.dualKompose_id

postfix:max "ᵒᵖ" =>
  Fam.Cat.Dual



/-- Double dualification is identity. -/
@[simp]
theorem Fam.Cat.idemDual
  (ℂ : Cat)
: (ℂᵒᵖ)ᵒᵖ = ℂ :=
  rfl
