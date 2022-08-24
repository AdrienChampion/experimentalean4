import Cat.Fam.Comp



/-! # Equivalence for category arrows in terms of the corresponding setoid -/

namespace Cat



/-- A proof that `f` is equivalent to `g` (`≋`, `\~~~`). -/
inductive Fam.Cat.Hom.Equiv
  {ℂ : Cat}
  {α β : ℂ.Obj}
  (f : α ↠ β)
: {γ δ : ℂ.Obj}
  → (γ ↠ δ)
  → Prop
where
| proof :
  (g : α ↠ β)
  → f ≈ g
  → Equiv f g


/-- Predicate for *"`f` and `g` are equivalent"* (`≋`, `\~~~`). -/
abbrev Fam.Cat.Hom.Equiv.equiv
  {ℂ : Cat}
  {α β γ δ : ℂ.Obj}
  (f : α ↠ β)
  (g : γ ↠ δ)
: Prop :=
  @Equiv ℂ α β f γ δ g

infix:30 " ≋ " =>
  Fam.Cat.Hom.Equiv.equiv



theorem Fam.Cat.Hom.Equiv.domEq
  {ℂ : Cat}
  {α β γ δ : ℂ.Obj}
  {f : α ↠ β}
  {g : γ ↠ δ}
  (h : f ≋ g)
: α = γ :=
  by
    cases h with
    | proof _ _ =>
      rfl

theorem Fam.Cat.Hom.Equiv.codEq
  {ℂ : Cat}
  {α β γ δ : ℂ.Obj}
  {f : α ↠ β}
  {g : γ ↠ δ}
  (h : f ≋ g)
: β = δ :=
  by
    cases h with
    | proof _ _ =>
      rfl



/-- Rewrites a `Equiv.proof` unifying (co)domains. -/
theorem Fam.Cat.Hom.Equiv.unify
  {ℂ : Cat}
  {α β γ δ : ℂ.Obj}
  {f : α ↠ β}
  {g : γ ↠ δ}
  (h : f ≋ g)
: (
  @Equiv ℂ α β f α β (
    let h_dom := domEq h
    let h_cod := codEq h
    by
      rw [h_dom, h_cod]
      exact g
  )
) :=
  by
    cases h with
    | proof g eq =>
      apply proof g eq

theorem Fam.Cat.Hom.Equiv.toEq
  {ℂ : Cat}
  {α β : ℂ.Obj}
  {f : α ↠ β}
  {g : α ↠ β}
  (h : f ≋ g)
: (f ≈ g) :=
  match h with
  | proof _ eq =>
    eq



/-! ## `Fam.Cat.Hom.Equiv` is an equivalence relation

We cannot build an `Equivalence` though, as it takes a `r : α → α → Prop`. `Equiv`'s arguments do
not have the same type in general `:/`.

We can still prove that `Equiv` is reflexive, symmetric and transitive so let's just do that.
-/
namespace Fam.Cat.Hom.Equiv

  theorem refl
    {ℂ : Cat}
    {α β : ℂ.Obj}
    (f : α ↠ β)
  : f ≋ f :=
    let eq_f :=
      ℂ.Hom α β |>.refl f
    proof f eq_f

  theorem symm
    {ℂ : Cat}
    {α₁ β₁ α₂ β₂ : ℂ.Obj}
    (f₁ : α₁ ↠ β₁)
    (f₂ : α₂ ↠ β₂)
  : f₁ ≋ f₂ → f₂ ≋ f₁ :=
    by
      intro h
      cases h
      apply proof
      apply ℂ.Hom α₁ β₁ |>.symm
      assumption

  theorem trans
    {ℂ : Cat}
    {α₁ β₁ α₂ β₂ α₃ β₃ : ℂ.Obj}
    {f₁ : α₁ ↠ β₁}
    {f₂ : α₂ ↠ β₂}
    {f₃ : α₃ ↠ β₃}
  : f₁ ≋ f₂ → f₂ ≋ f₃ → f₁ ≋ f₃ :=
    by
      intro h₁₂ h₂₃
      cases h₁₂ ; cases h₂₃
      apply proof
      apply ℂ.Hom α₁ β₁ |>.trans
      <;> assumption

end Fam.Cat.Hom.Equiv

instance instTransHomEq
  {ℂ : Fam.Cat}
  {α₁ β₁ α₂ β₂ α₃ β₃ : ℂ.Obj}
: Trans
  (@Fam.Cat.Hom.Equiv.equiv ℂ α₁ β₁ α₂ β₂)
  (@Fam.Cat.Hom.Equiv.equiv ℂ α₂ β₂ α₃ β₃)
  (@Fam.Cat.Hom.Equiv.equiv ℂ α₁ β₁ α₃ β₃)
where
  trans :=
    Fam.Cat.Hom.Equiv.trans
