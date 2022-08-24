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
  (F : Func ℂ₁ ℂ₂)
  {α β : ℂ₁.Obj}
: (α ↠ β) → (F.fObj α ↠ F.fObj β) :=
  fun f =>
    F.fMap f



/-- Allows writing `F object` for `F.fObj object` -/
instance instCoeFunFunctorObj
  {ℂ₁ ℂ₂ : Fam.Cat}
: CoeFun
  (Fam.Cat.Func ℂ₁ ℂ₂)
  (𝕂 $ ℂ₁.Obj → ℂ₂.Obj)
where
  coe F :=
    F.fObj

example
  (F : Fam.Cat.Func ℂ₁ ℂ₂)
  (α : ℂ₁.Obj)
: ℂ₂.Obj :=
  F α



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
theorem Fam.Cat.Func.fMap_proper
  (F : Func ℂ₁ ℂ₂)
  {α β : ℂ₁.Obj}
  (f₁ f₂ : α ↠ β)
: f₁ ≈ f₂ → F.fMap f₁ ≈ F.fMap f₂ :=
  F.fMap.proper

/-- `fmap` is proper for `≈`. -/
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
      Fam.Cat.Func.equiv F G

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

  instance instTransFuncEquiv
  : Trans
    (@Fam.Cat.Func.equiv ℂ₁ ℂ₂)
    (@Fam.Cat.Func.equiv ℂ₁ ℂ₂)
    (@Fam.Cat.Func.equiv ℂ₁ ℂ₂)
  where
    trans :=
      Fam.Cat.Func.Equiv.trans

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

  /-- `HomFunc.hom α f` is a morphism. -/
  @[simp]
  def Fam.Cat.Func.FunSET.HomFunc.morph
    (α : ℂ.Obj)
    (f : β ↠ γ)
  : (ℂ.Hom α β) ⇒ (ℂ.Hom α γ) where
    map :=
      hom α f
    proper :=
      ℂ.congr.right f



  /-- `HomFunc.morph α` is also a morphism.
  
  `HomFunc.Morph` will be the arrow-map in the `FunSET` functor below.
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



/-! ## Composition `⊙` (`\o.`) of two functors -/
section comp
  variable
    {ℂ₁ ℂ₂ ℂ₃ : Fam.Cat}
    (F₂₃ : Fam.Cat.Func ℂ₂ ℂ₃)
    (F₁₂ : Fam.Cat.Func ℂ₁ ℂ₂)

  @[simp]
  protected abbrev Fam.Cat.Func.comp.fObj
    (α : ℂ₁.Obj)
  :=
    F₁₂ α
    |> F₂₃

  @[simp]
  protected abbrev Fam.Cat.Func.comp.fmap
    {α β : ℂ₁.Obj}
    (f : α ↠ β)
  : F₂₃ (F₁₂ α) ↠ F₂₃ (F₁₂ β) :=
    F₁₂.fmap f
    |> F₂₃.fmap

  protected theorem Fam.Cat.Func.comp.fMap_proper
    {α β : ℂ₁.Obj}
    {f₁ f₂ : α ↠ β}
  : f₁ ≈ f₂ → Func.comp.fmap F₂₃ F₁₂ f₁ ≈ Func.comp.fmap F₂₃ F₁₂ f₂ :=
    fun h_f =>
      F₁₂.fMap.proper h_f
      |> F₂₃.fMap.proper



  /-- `Func.comp.fMap` defines a morphism. -/
  @[simp]
  protected def Fam.Cat.Func.comp.fMapMorph
    {α β : ℂ₁.Obj}
  : ℂ₁.Hom α β ⇒ ℂ₃.Hom (F₂₃ $ F₁₂ α) (F₂₃ $ F₁₂ β) where
    map :=
      Func.comp.fmap F₂₃ F₁₂
    proper :=
      Func.comp.fMap_proper F₂₃ F₁₂



  /-- Functor composition respects the functor composition law. -/
  protected def Fam.Cat.Func.comp.comp_law
    {α β γ : ℂ₁.Obj}
    (f : β ↠ γ)
    (g : α ↠ β)
  : Func.law.comp (Func.comp.fObj F₂₃ F₁₂) (Func.comp.fMapMorph F₂₃ F₁₂) f g :=
    by
      calc
        F₂₃.fMap.map
          (F₁₂.fMap.map (f ⊚ g))
        ≈ F₂₃.fMap.map
          ((F₁₂.fMap.map f) ⊚ (F₁₂.fMap.map g))
        :=
          F₁₂.comp_law f g
          |> F₂₃.fMap.proper
        
        _
        ≈ (F₂₃.fMap.map $ F₁₂.fMap.map f) ⊚ (F₂₃.fMap.map $ F₁₂.fMap.map g)
        :=
          by
            simp

  /-- Functor composition respects the functor identity law. -/
  protected def Fam.Cat.Func.comp.id_law
    {α : ℂ₁.Obj}
  : Func.law.id' (Func.comp.fObj F₂₃ F₁₂) (Func.comp.fMapMorph F₂₃ F₁₂) α :=
    by
      calc
        F₂₃.fMap.map (F₁₂.fMap.map ℂ₁.id)
        ≈ F₂₃.fMap.map ℂ₂.id
        :=
          F₂₃.fMap.proper (F₁₂.id_law)
        
        _
        ≈ ℂ₃.id
        :=
          F₂₃.id_law



  /-- Functor composition defines a functor (`⊙`, `\o.`). -/
  def Fam.Cat.Func.Comp
    (F₂₃ : Func ℂ₂ ℂ₃)
    (F₁₂ : Func ℂ₁ ℂ₂)
  : Func ℂ₁ ℂ₃ where
    fObj :=
      Func.comp.fObj F₂₃ F₁₂
    fMap :=
      Func.comp.fMapMorph F₂₃ F₁₂
    comp_law :=
      Fam.Cat.Func.comp.comp_law F₂₃ F₁₂
    id_law :=
      Fam.Cat.Func.comp.id_law F₂₃ F₁₂

  infix:101 " ⊙ " =>
    Fam.Cat.Func.Comp


  def Fam.Cat.Func.Comp.congr_right
    (F₂₃ : Func ℂ₂ ℂ₃)
    (F₁₂ F₁₂' : Func ℂ₁ ℂ₂)
    (h₁₂ : F₁₂ ≈ F₁₂')
  : F₂₃ ⊙ F₁₂ ≈ F₂₃ ⊙ F₁₂' :=
    by
      -- let ⟨fObj₁, fMap₁, comp_law₁, id_law₁⟩ :=
      --   F₁₂
      -- let ⟨fObj₁', fMap₁', comp_law₁', id_law₁'⟩ :=
      --   F₁₂'
      -- let ⟨fObj₂, fMap₂, comp_law₂, id_law₂⟩ :=
      --   F₂₃
      intro α β f
      let h :=
        h₁₂ f
      let h' :=
        h.unify
      simp [Eq.mpr, fmap] at h'
      cases h'
      match h' with
      | Hom.Equiv.proof _ eqv =>
        simp [fmap, Fam.Cat.Func.Comp]
        let eqv₂₃ :=
          F₂₃.fMap.proper eqv
        let p :=
          Hom.Equiv.proof _ eqv₂₃
        sorry


  /-- `Func.CompFunc` respects congruence laws. -/
  def Fam.Cat.Func.Comp.Congr
  : Congr (Func ℂ₂ ℂ₃) (Func ℂ₁ ℂ₂) (Func ℂ₁ ℂ₃) Func.Comp where
    left {F₂₃ F₂₃'} F₁₂ h₂₃ :=
      by
        intro α β f
        apply h₂₃
    right F₂₃ {F₁₂ F₁₂'} h₁₂ {α β} f :=
      by
        let h :=
          h₁₂ f
        sorry

end comp
