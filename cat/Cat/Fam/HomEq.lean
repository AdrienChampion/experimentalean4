import Cat.Fam.Comp



/-! # Equality for category arrows in terms of the corresponding setoid -/

namespace Cat



/-- A proof that `f` is equal to `g` (`≋`, `\~~~`). -/
inductive Fam.Cat.Hom.Equal
  {ℂ : Cat}
  {α β : ℂ.Obj}
  {f : |ℂ.Hom α β|}
: (γ δ : ℂ.Obj) → (g : |ℂ.Hom γ δ|) → Prop where
| proof :
  (g : |ℂ.Hom α β|)
  → f ≈ g
  → @Equal ℂ α β f α β g

/-- Predicate for *"`f` and `g` are equal"* (`≋`, `\~~~`). -/
@[simp]
abbrev Fam.Cat.Hom.Equal.equiv
  {ℂ : Cat}
  {α β γ δ : ℂ.Obj}
  (f : |ℂ.Hom α β|)
  (g : |ℂ.Hom γ δ|)
: Prop :=
  @Equal ℂ _ _ f _ _ g

infix:30 " ≋ " =>
  Fam.Cat.Hom.Equal.equiv



/-! ## `Fam.Cat.Hom.Equal` is an equivalence relation

We cannot build an `Equivalence` though, as it takes a `r : α → α → Prop`. `Equal`'s arguments do
not have the same type in general `:/`.

We can still prove that `Equal` is reflexive, symmetric and transitive so let's just do that.
-/
namespace Fam.Cat.Hom.Equal

  theorem refl
    {ℂ : Cat}
    {α β : ℂ.Obj}
    (f : |ℂ.Hom α β|)
  : f ≋ f :=
    let eq_f :=
      ℂ.Hom α β |>.refl f
    proof f eq_f

  theorem symm
    {ℂ : Cat}
    {α₁ β₁ α₂ β₂ : ℂ.Obj}
    (f₁ : |ℂ.Hom α₁ β₁|)
    (f₂ : |ℂ.Hom α₂ β₂|)
  : f₁ ≋ f₂ → f₂ ≋ f₁ :=
    by
      intro h
      cases h
      apply proof
      apply ℂ.Hom α₁ β₁ |>.symm
      assumption

  theorem trans
    {ℂ : Cat}
    {α₁ β₁ α₂ β₂ α₃ β₃}
    (f₁ : |ℂ.Hom α₁ β₁|)
    (f₂ : |ℂ.Hom α₂ β₂|)
    (f₃ : |ℂ.Hom α₃ β₃|)
  : f₁ ≋ f₂ → f₂ ≋ f₃ → f₁ ≋ f₃ :=
    by
      intro h₁₂ h₂₃
      cases h₁₂ ; cases h₂₃
      apply proof
      apply ℂ.Hom α₁ β₁ |>.trans
      <;> assumption
end Fam.Cat.Hom.Equal
