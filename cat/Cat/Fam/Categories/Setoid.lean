import Cat.Fam.CatLemmas



/-! # Category of setoids -/

namespace Cat



variable
  {α β γ δ : Setoid}



theorem Morph.compose_congr_left
  {f₁ f₂ : β ⇒ γ}
  (g : α ⇒ β)
: f₁ ≈ f₂ → f₁ ∘M g ≈ f₂ ∘M g :=
  fun h_f a =>
    g.map a
    |> h_f

theorem Morph.compose_congr_right
  (f : β ⇒ γ)
  {g₁ g₂ : α ⇒ β}
: g₁ ≈ g₂ → f ∘M g₁ ≈ f ∘M g₂ :=
  fun h_g a =>
    h_g a
    |> f.proper

-- theorem Morph.compose.Comp
-- : Fam.Comp Setoid Morph.mkSetoid where
--   comp :=
--     Morph.kompose
