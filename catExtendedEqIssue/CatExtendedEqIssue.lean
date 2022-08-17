/-! # Dependent elimination failure -/



/-- Equivalence between two functions with possibly different (co)domains.

The only constructor (`proof`) only allows constructing values where both functions *i)* have the
same (co)domain and *ii)* are equal.
-/
inductive MyEq
  {α β : Type u}
  (f : α → β)
: {γ δ : Type u}
  → (g : γ → δ)
  → Prop
where
| proof : (g : α → β) → (eq : f = g) → @MyEq α β f α β g

/-- Erases the domain and codomain of a function. -/
structure EFun where
  dom : Type u
  cod : Type u
  app : dom → cod

/-- Equivalence over `EFun` using `MyEq`. -/
abbrev EFun.equiv
  (f₁ f₂ : EFun)
: Prop :=
  @MyEq f₁.dom f₁.cod f₁.app f₂.dom f₂.cod f₂.app

/-- Give access to `≈` (`\~~`) notation for `EFun.equiv`. -/
instance : HasEquiv EFun where
  Equiv :=
    EFun.equiv



/-- Extracts `EFun` domain equality from the equivalence of two functions. -/
abbrev EFun.equiv.eqDom
  {f₁ f₂ : EFun}
  (h : f₁ ≈ f₂)
: f₁.dom = f₂.dom :=
  by
    cases h
    -- dependent elimination failed, failed to solve equation
    --   f₂.1 = f₁.1
    sorry
