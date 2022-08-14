import Cat.Fam.CatLemmas

/-! # Functors -/

namespace Cat



section laws

  variable
    {ℂ₁ ℂ₂ : Fam.Cat}
    (fObj : ℂ₁.Obj → ℂ₂.Obj)
    (fMap :
      {α β : ℂ₁.Obj}
      → ℂ₁.Hom α β ⇒ ℂ₂.Hom (fObj α) (fObj β)
    )

  /-- Functor composition law. -/
  @[simp]
  abbrev Fam.Cat.Func.law.comp
    {α β γ : ℂ₁.Obj}
    (f : β ↠ γ)
    (g : α ↠ β)
  : Prop :=
    fMap (f ⊚ g) ≈ (fMap f) ⊚ (fMap g)

  /-- Functor identity law. -/
  @[simp]
  protected abbrev Fam.Cat.Func.law.id
    {α : ℂ₁.Obj}
  : Prop :=
    @fMap α α ℂ₁.id ≈ ℂ₂.id

  /-- Functor identity law (explicit version). -/
  @[simp]
  protected abbrev Fam.Cat.Func.law.id'
    (α : ℂ₁.Obj)
  : Prop :=
    @law.id ℂ₁ ℂ₂ fObj fMap α

end laws



/-- A functor transforms objects/arrows and respects composition/identity laws.  -/
structure Fam.Cat.Func (ℂ₁ ℂ₂ : Cat) where
  /-- Maps `ℂ`-objects to `ℂ₂`-objects. -/
  fObj : ℂ₁.Obj → ℂ₂.Obj
  /-- Maps `ℂ₁`-arrows to `ℂ₂`-arrows. -/
  fMap :
    {α β : ℂ₁.Obj}
    → ℂ₁.Hom α β ⇒ ℂ₂.Hom (fObj α) (fObj β)
  /-- Functor composition law. -/
  comp_law
    {α β γ : ℂ₁.Obj}
    (f : β ↠ γ)
    (g : α ↠ β)
  : Func.law.comp fObj fMap f g
  /-- Functor identity law. -/
  id_law
    {α : ℂ₁.Obj}
  : Func.law.id' fObj fMap α

/-- Maps `ℂ₁`-arrows to `ℂ₂`-arrows (explicit version). -/
@[simp]
abbrev Fam.Cat.Func.fMap'
  {F : Func ℂ₁ ℂ₂}
  (α β : ℂ₁.Obj)
:=
  F.fMap (α := α) (β := β)

/-- Functor composition law (explicit version). -/
@[simp]
abbrev Fam.Cat.Func.comp_law'
  {F : Func ℂ₁ ℂ₂}
  (α β γ : ℂ₁.Obj)
:=
  @Func.comp_law ℂ₁ ℂ₂ F α β γ

/-- Functor identity law (explicit version). -/
@[simp]
abbrev Fam.Cat.Func.id_law'
  {F : Func ℂ₁ ℂ₂}
  (α : ℂ₁.Obj)
:=
  @Func.id_law ℂ₁ ℂ₂ F α

/-- Applied version of `F.fMap`. -/
def Fam.Cat.Func.fmap
  {F : Func ℂ₁ ℂ₂}
  {α β : ℂ₁.Obj}
: (α ↠ β) → (F.fObj α ↠ F.fObj β) :=
  fun f =>
    F.fMap f



-- /-- Allows writing `F object` for `F.fObj object` -/
-- instance instCoeFunFunctorObj
--   {ℂ₁ ℂ₂ : Fam.Cat}
-- : CoeFun
--   (Fam.Cat.Func ℂ₁ ℂ₂)
--   (𝕂 $ ℂ₁.Obj → ℂ₂.Obj)
-- where
--   coe F :=
--     F.fObj

-- example
--   (F : Fam.Cat.Func ℂ₁ ℂ₂)
--   (α : ℂ₁.Obj)
-- : ℂ₂.Obj :=
--   F α



-- /-- Allows writing `F hom` for `F.fmap hom`. -/
-- instance instCoeFunFunctorHom
--   {ℂ₁ ℂ₂ : Fam.Cat}
--   {α β : ℂ₁.Obj}
-- : CoeFun
--   (Fam.Cat.Func ℂ₁ ℂ₂)
--   (fun F =>
--     (α ↠ β) → (F.fObj α ↠ F.fObj β)
--   )
-- where
--   coe F :=
--     F.fmap

-- example
--   (F : Fam.Cat.Func ℂ₁ ℂ₂)
--   (f : α ↠ β)
-- : F.fObj α ↠ F.fObj β :=
--   F f



/-- `fMap` is proper for `≈`. -/
theorem Fam.Cat.Func.fmap_proper
  (F : Func ℂ₁ ℂ₂)
  {α β : ℂ₁.Obj}
  (f₁ f₂ : α ↠ β)
: f₁ ≈ f₂ → F.fmap f₁ ≈ F.fmap f₂ :=
  F.fMap.proper



/-! ## Setoid of functors -/
section setoid
  variable
    {ℂ₁ ℂ₂ : Fam.Cat}
    (F G : Fam.Cat.Func ℂ₁ ℂ₂)

  /-- Functor equivalence is `fmap` equivalence. -/
  @[simp]
  abbrev Fam.Cat.Func.equiv
  : Prop :=
    ∀ {α β : ℂ₁.Obj} (f : α ↠ β), F.fmap f ≋ G.fmap f

  instance instFuncHasEquiv
  : HasEquiv (Fam.Cat.Func ℂ₁ ℂ₂) where
    Equiv F G :=
      @Fam.Cat.Func.equiv ℂ₁ ℂ₂ F G

  /-- Functor equivalence is reflexive. -/
  theorem Fam.Cat.Func.Equiv.refl
  : F ≈ F :=
    fun f =>
      F.fmap f
      |> Hom.Equiv.refl

  /-- Functor equivalence is symmetric. -/
  theorem Fam.Cat.Func.Equiv.symm
    {F G : Func ℂ₁ ℂ₂}
  : F ≈ G → G ≈ F :=
    fun h_FG _α _β f =>
      h_FG f
      |> Hom.Equiv.symm (F.fmap f) (G.fmap f)

  /-- Functor equivalence is transitive. -/
  theorem Fam.Cat.Func.Equiv.trans
    {F G H : Func ℂ₁ ℂ₂}
  : F ≈ G → G ≈ H → F ≈ H :=
    fun h_FG h_GH _α _β f =>
      Hom.Equiv.trans
        (h_FG f)
        (h_GH f)

  /-- Functor equivalence is an equivalence relation. -/
  def Fam.Cat.Func.Equiv.proof
  : Equivalence (@Fam.Cat.Func.equiv ℂ₁ ℂ₂) :=
    ⟨refl, symm, trans⟩



  /-- Functors are setoids in the Lean sense. -/
  instance instZetoidFunc
  : Zetoid (Fam.Cat.Func ℂ₁ ℂ₂) where
    r :=
      Fam.Cat.Func.equiv
    iseqv :=
      Fam.Cat.Func.Equiv.proof

  /-- Functors are setoids in this library's sense. -/
  def Fam.Cat.Func.mkSetoid
    (ℂ₁ ℂ₂ : Cat)
  : Setoid where
    Carrier :=
      Func ℂ₁ ℂ₂
    instZetoid :=
      instZetoidFunc

end setoid
