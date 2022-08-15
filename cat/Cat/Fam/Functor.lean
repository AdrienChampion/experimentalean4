import Cat.Fam.CatLemmas
import Cat.Fam.Categories.Setoid

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



/-! ## Family of Hom-functors

Functor `Hom(α,-) : ℂ → Set`. Basically, this functor
- maps `β : ℂ.Obj` to `ℂ.Hom α β`;
- maps `f : ℂ.Hom β γ` to `fun (g : ℂ.Hom α β) => f ∘ g`.

So `α` is a kind of pivot we see `ℂ` through: a `β` only matters as far as we can go from `α` to
`β`, and a `ℂ.Hom β γ` only matters as far as we can compose it with a `ℂ.Hom α β`.
-/
section hom_functors
  variable
    {ℂ : Fam.Cat}
    {α : ℂ.Obj}

  @[simp]
  abbrev Fam.Cat.Func.FunSET.HomFunc.obj
    (α β : ℂ.Obj)
  :=
    ℂ.Hom α β

  @[simp]
  abbrev Fam.Cat.Func.FunSET.HomFunc.hom
    (α : ℂ.Obj)
    {β γ : ℂ.Obj}
    (f : β ↠ γ)
    (g : α ↠ β)
  : α ↠ γ :=
    f ⊚ g

  /-- `HomFunc.hom` is a morphism. -/
  @[simp]
  def Fam.Cat.Func.FunSET.HomFunc.morph
    (α : ℂ.Obj)
    (f : β ↠ γ)
  : (ℂ.Hom α β) ⇒ (ℂ.Hom α γ) where
    map :=
      hom α f
    proper :=
      ℂ.congr.right f



  /-- `HomFunc.morph` is itself a morphism.
  
  `HomFunc.Morph` will be the arrow-mapping in the `FunSET` functor.
  -/
  @[simp]
  def Fam.Cat.Func.FunSET.HomFunc.Morph
    (α : ℂ.Obj)
    {β γ : ℂ.Obj}
  : (ℂ.Hom β γ) ⇒ (Fam.Cat.SET.Hom (HomFunc.obj α β) (HomFunc.obj α γ)) where
    map f :=
      HomFunc.morph α f
    proper :=
      by
        intro f₁ f₂ h_f
        simp
        intro g
        apply ℂ.congr.left g h_f

  /-- `HomFunc.Morph` respects the composition law. -/
  theorem Fam.Cat.Func.FunSET.HomFunc.Morph.comp_law
    (α : ℂ.Obj)
    {β γ δ : ℂ.Obj}
    (g : γ ↠ δ)
    (h : β ↠ γ)
  : law.comp (ℂ₁ := ℂ) (ℂ₂ := SET) (obj α) (Morph α) g h :=
    by
      intro param
      simp [
        kompose, compose',
        SET, Comp.toCat, Morph.app2,
        Morph.compose.Comp, Morph.compose
      ]

  /-- `HomFunc.Morph` respects the identity law. -/
  theorem Fam.Cat.Func.FunSET.HomFunc.Morph.id_law
    (α β : ℂ.Obj)
  : law.id' (ℂ₁ := ℂ) (ℂ₂ := SET) (obj α) (Morph α) β :=
    by
      intro f
      simp [
        SET, Comp.toCat,
        Morph.id,
        kompose, compose',
        Morph.app2
      ]



  /-- Hom-functors are functors. -/
  def Fam.Cat.Func.FunSET
    {ℂ : Cat}
    (α : ℂ.Obj)
  : Func ℂ SET where
    fObj :=
      Fam.Cat.Func.FunSET.HomFunc.obj α
    fMap :=
      FunSET.HomFunc.Morph α
    comp_law :=
      FunSET.HomFunc.Morph.comp_law α
    id_law :=
      @FunSET.HomFunc.Morph.id_law _ α

end hom_functors
