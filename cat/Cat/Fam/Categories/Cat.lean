import Cat.Fam.Functor



/-! # The category of categories -/

namespace Cat



variable
  (ℂ₁ ℂ₂ ℂ₃ : Fam.Cat)
  (F₁₂ : Fam.Cat.Func ℂ₁ ℂ₂)
  (F₂₃ : Fam.Cat.Func ℂ₂ ℂ₃)
