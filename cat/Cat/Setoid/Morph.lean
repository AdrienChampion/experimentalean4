import Cat.Setoid.Setoid



/-! # Morphisms between setoids, seen as setoids over functions
-/

namespace Cat



/-- Notion of morphism over `Setoid` (`⇒`, `\r=`). -/
structure Morph.{ua, ub}
  (α : Setoid.{ua})
  (β : Setoid.{ub})
: Type (max ua ub) where

  /-- Maps values from `α`'s carrier to values of `β`'s carrier. -/
  map : |α| → |β|

  /-- `map` is proper for setoid equivalence (`≈`). -/
  proper {a₁ a₂ : |α|} :
    a₁ ≈ a₂ → map a₁ ≈ map a₂

infixr:3 " ⇒ " =>
  Morph



section Morph

  universe u_α u_β

  variable
    {α : Setoid.{u_α}}
    {β : Setoid.{u_β}}

  /-- Domain accessor. -/
  def Morph.dom
    (_ : α ⇒ β)
  : Setoid.{u_α} :=
    α
  /-- Codomain accessor. -/
  def Morph.cod
    (_ : α ⇒ β)
  : Setoid.{u_β} :=
    β

  /-- Applies the underlying function. -/
  def Morph.app
    (self : α ⇒ β)
  : |α| → |β| :=
    (self.map ·)


  /-! ## Equivalence relation on morphisms -/
  section equiv

    /-- Equivalence relation (extensional equality, `≈`, `\~~`). -/
    abbrev Morph.equiv
      {α β : Setoid}
      (f g : α ⇒ β)
    : Prop :=
      ∀ (a : |α|), f.map a ≈ g.map a

    /-- Give access to `≈` (`\~~`) equivalence notation. -/
    instance instHasEquivMorph
    : HasEquiv (α ⇒ β) where
      Equiv :=
        Morph.equiv

    /-- `Morph.equiv` is reflexive. -/
    def Morph.equiv.refl
      (m : α ⇒ β)
    : m ≈ m :=
      (m.map · |> β.refl)

    /-- `Morph.equiv` is symmetric. -/
    def Morph.equiv.symm
      {f g : α ⇒ β}
      (h : f ≈ g)
    : g ≈ f :=
      (h · |> β.symm)

    /-- `Morph.equiv` is transitive. -/
    def Morph.equiv.trans
      {f g h : α ⇒ β}
      (eqFG : f ≈ g)
      (eqGH : g ≈ h)
    : f ≈ h :=
      fun a =>
        β.trans (eqFG a) (eqGH a)

    /-- `Morph.equiv` is an equivalence relation. -/
    def Morph.equiv.iseqv
    : @Equivalence (α ⇒ β) Morph.equiv :=
      ⟨refl, symm, trans⟩



    instance instTransMorphEquiv
      {α β : Setoid}
    : let I := @instHasEquivMorph α β
      Trans I.Equiv I.Equiv I.Equiv
    where
      trans :=
        Morph.equiv.trans

  end equiv



  /-- Composition of two morphisms, `Morph` version (`∘M`). -/
  def Morph.compose
    (f : β ⇒ γ)
    (g : α ⇒ β)
  : α ⇒ γ where
    map :=
      f.map ∘ g.map
    proper :=
      f.proper ∘ g.proper

  infix:100 " ∘M " =>
    Morph.compose

  /-- Morphism composition (`∘M`) is associative. -/
  theorem Morph.compose.assoc
    (f : γ ⇒ δ)
    (g : β ⇒ γ)
    (h : α ⇒ β)
  : f ∘M (g ∘M h) ≈ (f ∘M g) ∘M h :=
    fun a =>
      by simp [compose, δ.refl]

  /-- Morphism composition (`∘M`) abides by congruence laws. -/
  def Morph.compose.congr
  : Congr (β ⇒ γ) (α ⇒ β) (α ⇒ γ) Morph.compose where
    left g :=
      fun h_f a =>
        g.map a |> h_f
    right f :=
      fun h_g a =>
        h_g a |> f.proper




  /-- Composition of two morphisms, function version (`∘m`). -/
  def Morph.kompose
    (f : β ⇒ γ)
    (g : α ⇒ β)
  : |α| → |γ| :=
    (f.compose g).map

  infix:100 " ∘m " =>
    Morph.kompose

  /-- Morphism composition (`∘M`) is associative. -/
  theorem Morph.kompose.assoc
    (f : γ ⇒ δ)
    (g : β ⇒ γ)
    (h : α ⇒ β)
  : f ∘M (g ∘M h) ≈ (f ∘M g) ∘M h :=
    fun a =>
      by simp [compose, δ.refl]



  /-- Identity morphism over an implicit erased setoid `α`. -/
  protected def Morph.id
    {α : Setoid}
  : α ⇒ α where
    map := id
    proper := id

  /-- Identity morphism over an explicit erased setoid `α`. -/
  protected abbrev Morph.id'
    (α : Setoid)
  : α ⇒ α :=
    @Morph.id α

  /-- `Morph.id` is a left-identity for `∘M`. -/
  theorem Morph.id_compose
    (f : α ⇒ β)
  : Morph.id ∘M f ≈ f :=
    fun _a =>
      β.refl _

  /-- `Morph.id` is a right-identity for `∘M`. -/
  theorem Morph.compose_id
    (f : α ⇒ β)
  : f ∘M Morph.id ≈ f :=
    fun _a =>
      β.refl _



  /-! ## `Morph` as a `Setoid` -/
  section MorSet

    /-- `Zetoid` instance so that we can build the actual `Setoid`. -/
    instance instZetoidMorph
    : Zetoid (α ⇒ β) where
      r :=
        Morph.equiv
      iseqv :=
        Morph.equiv.iseqv

    /-- Builds the `Setoid` for `α ⇒ β`, written `α ⇛ β` (`\r==`).

    Note that you should not need to write `|α ⇛ β|` since the carrier of `α ⇛ β` is simply `α ⇒ β`.
    It is however sometimes more readable to write `|α ⇛ β ⇛ γ|` for `α ⇒ β ⇛ γ`.
    -/
    def Morph.mkSetoid
      (α : Setoid.{u_a})
      (β : Setoid.{u_b})
    : Setoid where
      Carrier :=
        α ⇒ β
      instZetoid :=
        instZetoidMorph

    infixr:4 " ⇛ " =>
      Morph.mkSetoid

  end MorSet



  /-! ## More helpers, mostly for defining a first notion of category -/

  /-- Same as `app` but the codomain is a morphism. -/
  def Morph.app2
    {γ : Setoid.{u_γ}}
    (self : α ⇒ β ⇛ γ)
    -- (self : |α ⇛ β ⇛ γ|) -- alternatively, same as the above
    (a : |α|)
  : |β| → |γ| :=
    self.map a
    |>.map

  /-- Takes a composition operation over morphisms and returns the underlying binary function. -/
  def Morph.komposeExt
    {Obj : Sort u_o}
    {Hom : Obj → Obj → Setoid}
    (compose :
      (α β γ : Obj) → |Hom β γ ⇛ Hom α β ⇛ Hom α γ|)
    {α β γ : outParam Obj}
  : |Hom β γ| → |Hom α β| → |Hom α γ| :=
    compose α β γ
    |>.app2

  macro "⟦ " f:term " ⟧" : term =>
    `(Morph.komposeExt $f)

end Morph



/-! ## Some useful instances -/

/-- Allows using a `Morph` directly as its underlying function. -/
instance instCoeFunMorph
: CoeFun (α ⇒ β) (𝕂 $ |α| → |β|) where
  coe m :=
    m.map
/-- Allows using a `Morph` setoid directly as its underlying function. -/
instance instCoeFunMorphSetoid
: CoeFun (|α ⇛ β|) (𝕂 $ |α| → |β|) where
  coe m :=
    m.map
