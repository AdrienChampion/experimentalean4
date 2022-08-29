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
  : @fMap α α ℂ₁.id ≈ ℂ₂.id

/-- Identity for the target of a source object. -/
@[simp]
abbrev Fam.Cat.Func.id
  {F : Func ℂ₁ ℂ₂}
  {α : outParam ℂ₁.Obj}
: F.fObj α ↠ F.fObj α :=
  ℂ₂.id

/-- Identity for the target of a source object, explicit version. -/
@[simp]
abbrev Fam.Cat.Func.id'
  {F : Func ℂ₁ ℂ₂}
  (α : outParam ℂ₁.Obj)
: F.fObj α ↠ F.fObj α :=
  ℂ₂.id

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
  F.id_law (α := α)

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
  {f₁ f₂ : α ↠ β}
: f₁ ≈ f₂ → F.fMap f₁ ≈ F.fMap f₂ :=
  F.fMap.proper
/-- `fMap` is proper for `≈`, explicit version. -/
theorem Fam.Cat.Func.fMap_proper'
  (F : Func ℂ₁ ℂ₂)
  {α β : ℂ₁.Obj}
  (f₁ f₂ : α ↠ β)
: f₁ ≈ f₂ → F.fMap f₁ ≈ F.fMap f₂ :=
  F.fMap.proper

/-- `fmap` is proper for `≈`. -/
theorem Fam.Cat.Func.fmap_proper
  (F : Func ℂ₁ ℂ₂)
  {α β : ℂ₁.Obj}
  {f₁ f₂ : α ↠ β}
: f₁ ≈ f₂ → F.fmap f₁ ≈ F.fmap f₂ :=
  F.fMap.proper
/-- `fmap` is proper for `≈`. -/
theorem Fam.Cat.Func.fmap_proper'
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
  def Fam.Cat.Func.comp
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
    Fam.Cat.Func.comp



  theorem Fam.Cat.Func.comp.congr_left
    {F₂₃ F₂₃' : Func ℂ₂ ℂ₃}
    (F₁₂ : Func ℂ₁ ℂ₂)
    (h₂₃ : F₂₃ ≈ F₂₃')
  : F₂₃ ⊙ F₁₂ ≈ F₂₃' ⊙ F₁₂ :=
    fun f =>
      h₂₃ (F₁₂.fmap f)

  protected theorem Fam.Cat.Func.comp.congr_right_aux
    (F₂₃ : Func ℂ₂ ℂ₃)
    (F₁₂ : Func ℂ₁ ℂ₂)
    {α' β' : ℂ₂.Obj}
    (f₁₂' : α' ↠ β')
    {α β : ℂ₁.Obj}
    (f : α ↠ β)
    (h : F₁₂.fmap f ≋ f₁₂')
  : F₂₃.fmap (F₁₂.fmap f) ≋ F₂₃.fmap f₁₂' :=
    by
      cases h with
      | proof f₁₂' eqv =>
        let eqv₂₃ :=
          F₂₃.fMap.proper eqv
        apply Hom.Equiv.proof _ eqv₂₃

  theorem Fam.Cat.Func.comp.congr_right
    (F₂₃ : Func ℂ₂ ℂ₃)
    {F₁₂ F₁₂' : Func ℂ₁ ℂ₂}
    (h₁₂ : F₁₂ ≈ F₁₂')
  : F₂₃ ⊙ F₁₂ ≈ F₂₃ ⊙ F₁₂' :=
    fun f =>
      let h :=
        h₁₂ f
      comp.congr_right_aux F₂₃ F₁₂ (fmap F₁₂' f) f h


  /-- `Func.comp` respects congruence laws. -/
  def Fam.Cat.Func.comp.Congr
  : Congr (Func ℂ₂ ℂ₃) (Func ℂ₁ ℂ₂) (Func ℂ₁ ℂ₃) Func.comp where
    left :=
      congr_left
    right :=
      congr_right

end comp



section lemmas
  variable
    {ℂ₁ ℂ₂ : Fam.Cat}
    (F : Fam.Cat.Func ℂ₁ ℂ₂)



  theorem Fam.Cat.Func.proper_inv
    {α β : ℂ₁.Obj}
    {f₁ : α ↠ β}
    {f₂ : β ↠ α}
    (h : f₁ ⊚ f₂ ≈ ℂ₁.id)
  : (F.fMap f₁) ⊚ (F.fMap f₂) ≈ F.id :=
    let f₁' :=
      F.fMap f₁
    let f₂' :=
      F.fMap f₂
    let h₁ : f₁' ⊚ f₂' ≈ F.fMap (f₁ ⊚ f₂) :=
      F.comp_law f₁ f₂
      |> Setoid.symm
    let h₂ : f₁' ⊚ f₂' ≈ F.fMap ℂ₁.id :=
      F.fmap_proper h
      |> Setoid.trans h₁
    let h₃ : f₁' ⊚ f₂' ≈ ℂ₂.id :=
      F.id_law' β
      |> Setoid.trans h₂
    h₃

  /-- Functors preserve the *iso* property over arrows. -/
  instance instIsoFuncIso
    {F : Fam.Cat.Func ℂ₁ ℂ₂}
    {α β : ℂ₁.Obj}
    (f : α ↠ β)
    [instIso : Fam.Cat.Iso f]
  : Fam.Cat.Iso (F.fmap f) :=
    let fInv' :=
      F.fmap instIso.inv
    Fam.Cat.Iso.mk
      fInv'
      (F.proper_inv instIso.law_left)
      (F.proper_inv instIso.law_right)
  

  /-- Functors preserve the *iso* property over objects. -/
  instance instIsoObjFuncIsoObj
    {α β : ℂ₁.Obj}
    (h_iso : α ≅ β)
  : F α ≅ F β where
    iso :=
      F.fmap h_iso.iso
    instIso :=
      instIsoFuncIso h_iso.iso



  /-- Proof that a functor is *faithful*, *i.e.* `F f ≈ F g → f ≈ g`. -/
  class Fam.Cat.Func.Faithful
    {ℂ₁ ℂ₂ : Cat}
    (F : Func ℂ₁ ℂ₂)
  where
    /-- Faithfulness law. -/
    law' :
      ∀ {α β : ℂ₁.Obj} (f g : α ↠ β),
        F.fmap f ≈ F.fmap g → f ≈ g

  /-- Same as `Faithful.law'` but `f` and `g` are implicit. -/
  @[simp]
  abbrev Fam.Cat.Func.Faithful.law
    [inst : Faithful F]
    {α β : ℂ₁.Obj}
    {f g : α ↠ β}
  : F.fmap f ≈ F.fmap g → f ≈ g :=
    inst.law' f g

  /-- Faithfulness is closed under functor composition. -/
  instance instFaithfulFuncComp
    (F₂₃ : Fam.Cat.Func ℂ₂ ℂ₃)
    [inst₂₃ : Fam.Cat.Func.Faithful F₂₃]
    (F₁₂ : Fam.Cat.Func ℂ₁ ℂ₂)
    [inst₁₂ : Fam.Cat.Func.Faithful F₁₂]
  : Fam.Cat.Func.Faithful (F₂₃ ⊙ F₁₂) where
    law' {α β} (f g) h :=
      by
        apply inst₁₂.law
        apply inst₂₃.law
        exact h



  /-- Proof that a functor is *full*, *i.e.* any `h : F α ↠ F β` has a preimage by `F.fmap`. -/
  class Fam.Cat.Func.Full
    {ℂ₁ ℂ₂ : Cat}
    (F : Func ℂ₁ ℂ₂)
  where
    /-- Yields the preimage of `h` by `F.fmap`. -/
    preimage
      {α β : ℂ₁.Obj}
      (h : F α ↠ F β)
    : α ↠ β
    /-- Proof that `h` and the image of its preimage are equivalent. -/
    law'
      {α β : ℂ₁.Obj}
      (h : F α ↠ F β)
    : h ≈ F.fmap (preimage h)

  /-- Same as `Full.law'` but `h` is implicit. -/
  @[simp]
  abbrev Fam.Cat.Func.Full.law
    [inst : Full F]
    {α β : ℂ₁.Obj}
    {h : F α ↠ F β}
  : h ≈ F.fmap (inst.preimage h) :=
    inst.law' h

  /-- Fullness is closed under functor composition. -/
  instance instFullFuncComp
    (F₂₃ : Fam.Cat.Func ℂ₂ ℂ₃)
    [inst₂₃ : Fam.Cat.Func.Full F₂₃]
    (F₁₂ : Fam.Cat.Func ℂ₁ ℂ₂)
    [inst₁₂ : Fam.Cat.Func.Full F₁₂]
  : Fam.Cat.Func.Full (F₂₃ ⊙ F₁₂) where
    preimage h :=
      inst₂₃.preimage h
      |> inst₁₂.preimage
    law' g₃ :=
      let g₂ :=
        inst₂₃.preimage g₃
      let g₁ :=
        inst₁₂.preimage g₂
      let h : g₃ ≈ F₂₃.fmap g₂ :=
        inst₂₃.law
      let h' : g₂ ≈ F₁₂.fmap g₁ :=
        inst₁₂.law
      let h : g₃ ≈ F₂₃.fmap (F₁₂.fmap g₁) :=
        F₂₃.fmap_proper h'
        |> Setoid.trans h
      h

end lemmas
