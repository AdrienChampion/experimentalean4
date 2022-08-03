/-! # Categories with families

- <https://pdf.sciencedirectassets.com/272990/1-s2.0-S1571066108X03287/1-s2.0-S1571066108000431/main.pdf?X-Amz-Security-Token=IQoJb3JpZ2luX2VjEPn%2F%2F%2F%2F%2F%2F%2F%2F%2F%2FwEaCXVzLWVhc3QtMSJIMEYCIQDwSF1X%2BYO%2F420uK0n0MdZTtNU2%2B%2FDo5ql0cunor%2BFRewIhAJ4XOqT8wx%2BZAzPu8FBv2G6tz6E5ZWwiCtxrMsi6X2UEKtIECEIQBRoMMDU5MDAzNTQ2ODY1IgzjK4CqLFqIrVFPCUEqrwTnJTrTfLOTaY9k3Ch6O%2FSImGgJi0F7lkZDHIiBdgbeEStN4CpfodcMLuTFCmYzXcmYuzmkP%2FPJnxyvNcn5JrRLnaMewDE%2B3%2FGVoeYkVwCPjztK2DGe%2FsPV0RAVIIAnpwxDlOlbkXGsC3e7COE%2FOSf5fAuKjTzfdm5McO5%2B3sYtD8RkZQfex%2F7LNtLzy038RVAk06%2BUItTzCnkyVda%2F3D%2FSD3H5bGhXAoqx4npAWasoFiE%2FdK2Mc1sR2ctPrnNyA64eBGiPWMqcUC%2F2XP2%2Fqm6oOhzZ2mF%2BLaB939%2FKlHQW7cNpEI9pUK6nzVnCpLqvzJ%2F28yTN6JIMzhGTfyjeCqzwslLEGcnztnYJJarabqJNVz6vP8ZtuzitgE8U1RXtoznNUEvsf6WkqIIxUXFun2BetbEPKYWo03%2BY8513iWFUMjwUYA8qzmRqaKelG7mpBt2ethZ32OwA3A1sAyoieEl5F2hL39yQ4ci7OECkHaSdtcqfv9WOyx5yJyvR1tFDEeElXG%2BfDqwITeFX3Y5HYgqpgQnIO2j08O%2BxDWtFFmeDjrUlRIg%2FUYy3%2BjhOV1vCIWDK5DE%2BHDthVC8OQwZJsR7izuC8mnrQ6Uip8h6g7x%2Bi5Xj8ynsw9TJyG8uxZunW9W76VA%2BFtpwJvnjjK9qz5V3Mvw6TFC1kkkSU9tXDxol4oit51j0Kn%2B6DdZMFZ8xSCiScFp%2FWSmQbwc7P8Gj0Lc1G49Ta4PeJys4OIpj804UnMI6h5JYGOqgB0sUc2k7f5s6CwiuPaUtFtjOnuJ92Xbnyngs9my9kt8IEJfzf4YlOKQGSEAnb%2BY20id7AQ%2B1yEKJOTghF5n3VuxZrFAgm1UApCYelVTZVWpIR%2F4BlEjqK7eQXfHQcakfsShNZmxZaTb38s7XuaILIUtqSMzs%2FsDbgKeFlGbvmeh%2F4fHBmurgsRrRpoB82YAxmUtNWLpGgDb5jUstx5BRTki1xjbosnJHY&X-Amz-Algorithm=AWS4-HMAC-SHA256&X-Amz-Date=20220721T093450Z&X-Amz-SignedHeaders=host&X-Amz-Expires=300&X-Amz-Credential=ASIAQ3PHCVTYXTXEDTIG%2F20220721%2Fus-east-1%2Fs3%2Faws4_request&X-Amz-Signature=0affbbdd57922b0f96e28892245af10f9be3110f02ece17d8480d74994213d13&hash=f9d87630690a224ca4dbf56150bcb6d37ee97e58789a530871c3952447d85a86&host=68042c943591013ac2b2430a89b270f6af2c76d8dfd086a07176afe7c76c2c61&pii=S1571066108000431&tid=spdf-50948ff5-19da-4bb3-875f-03d9091e3445&sid=346b3b469d82e94daf8b1476084c2ca4555fgxrqb&type=client&ua=5755035c0153545c50&rr=72e2f1695ae23bb0>
-/



section erased_setoid

  /-- Erases the carrier of a `Setoid`.

  Instead of `Setoid α`, this structure stores `α` as `Carrier` alongside an instance of `Setoid
  Carrier`. This allows functions producing `Setoid.Erased` values to produce different carriers
  for different input values.
  -/
  structure Setoid.Erased
  where innermk ::
    Carrier : Sort c
    setoid : Setoid Carrier

  /-- Allow using `S : Setoid.Erased` directly as `S.Carrier`. -/
  instance instCoeSortSetoidErased
  : CoeSort Setoid.Erased (Sort c) where
    coe S :=
      S.Carrier

  /-- Bring `S.setoid` in scope whenever we handle `S.Carrier`. -/
  instance instSetoidSetoidErased
    {S : Setoid.Erased}
  : Setoid S.Carrier :=
    S.setoid

  /-- Give access to `α ≈ β` notation. -/
  instance instHasEquivSetoidErased
    (S : Setoid.Erased)
  : HasEquiv S.Carrier :=
    @instHasEquiv S.Carrier S.setoid


  /-! ## Basic operations for `Setoid.Erased` -/
  namespace Setoid.Erased
    /-- Constructor. -/
    def mk
      (Carrier : Type c)
      [setoid : Setoid Carrier]
    : Erased :=
      ⟨Carrier, setoid⟩

    /-! ### Lift stuff from inner `Setoid` instance -/

    variable
      (self : Erased)

    def r :=
      self.setoid.r

    def refl :=
      self.setoid.refl
    def symm
      {a b : self.Carrier}
    : a ≈ b → b ≈ a :=
      self.setoid.symm
    def trans
      {a b c : self.Carrier}
    : a ≈ b → b ≈ c → a ≈ c:=
      self.setoid.trans
  end Setoid.Erased

end erased_setoid



/-- A simple category, basis for categories with families. -/
structure Fam.Cat where
  Object : Sort o

  /-- This returns `Setoid.Erased` to allow dependent, arbitrary carriers. -/
  Arrow :
    Object → Object → Setoid.Erased

  /-- Arrow composition. -/
  compose {α β γ : Object} :
    Arrow β γ → Arrow α β → Arrow α γ
  /-- Arrow composition is associative. -/
  compose_assoc
    {α β γ δ : Object}
    (f : Arrow γ δ) (g : Arrow β γ) (h : Arrow α β)
  : compose f (compose g h)
  = compose (compose f g) h

  /-- Identity arrows. -/
  id {α : Object} :
    Arrow α α
  /-- `id` is a left-identity for `compose`. -/
  id_compose (f : Arrow α β) :
    compose id f = f
  /-- `id` is a right-identity for `compose`. -/
  compose_id (f : Arrow α β) :
    compose f id = f

def Fam.Cat.dual (cat : Cat) : Cat where
  Object :=
    cat.Object
  Arrow α β :=
    cat.Arrow β α

  compose f g :=
    cat.compose g f
  compose_assoc f g h :=
    cat.compose_assoc h g f
    |>.symm

  id :=
    cat.id
  id_compose :=
    cat.compose_id
  compose_id :=
    cat.id_compose

abbrev Fam.Cat.op :=
  Fam.Cat.dual



/-- Notion of morphism over `Setoid.Erased` (`⇒`). -/
structure Setoid.Erased.Morphism (α β : Setoid.Erased) where
  /-- Maps values from `α`'s carrier to values of `β`'s carrier. -/
  map : α → β
  /-- `map` is proper for `≈`. -/
  proper {a₁ a₂ : α} :
    a₁ ≈ a₂ → map a₁ ≈ map a₂

infix:min " ⇒ " => Setoid.Erased.Morphism



/-- Composition of two morphisms (`∘m`). -/
def Setoid.Erased.Morphism.compose
  (f : β ⇒ γ) (g : α ⇒ β)
: α ⇒ γ where
  map :=
    f.map ∘ g.map
  proper h :=
    g.proper h
    |> f.proper

infix:40 " ∘m " => Setoid.Erased.Morphism.compose



/-- Identity morphism over an explicit erased setoid `α`. -/
def Setoid.Erased.Morphism.id (α : Setoid.Erased) : Morphism α α where
  map := (·)
  proper := (·)
/-- Identity morphism over an implict erased setoid `α`. -/
abbrev Setoid.Erased.Morphism.id' {α : Setoid.Erased} :=
  id α

/-- Setoid morphism extensionality, not sure this is useful but whatever. -/
protected def Setoid.Erased.Morphism.funext
  {α β : Setoid.Erased}
  {m₁ m₂ : α ⇒ β}
  (h : ∀ (x : α), m₁.map x = m₂.map x)
: m₁.map = m₂.map :=
  funext (f₁ := m₁.map) (f₂ := m₂.map) h

/-- Extensional equality (`≋`) for morphisms. -/
abbrev Setoid.Erased.Morphism.exteq
  {α β : Setoid.Erased}
  (f g : α ⇒ β)
: Prop :=
  ∀ (a : α), f.map a ≈ g.map a

infix:min " ≋ " => Setoid.Erased.Morphism.exteq



/-- Family of setoids indexed by a given setoid `S`.

- `fibre`: indexes setoids by elements of `S`'s carrier;
- `ι`: re-indexing function, maps `S`'s equivalence relation into morphisms over the indexed
  setoids.
-/
structure Fam
  (S : Setoid.Erased)
where
  /-- Indexes setoids by elements of `S`'s carrier. -/
  fibre : S → Setoid.Erased
  /-- Re-indexing function, maps `S`'s equivalence relation into morphisms over indexed setoids. -/
  ι :
    {x x' : S} → (x ≈ x') → (fibre x' ⇒ fibre x)

  /-- `ι` of the same index yields the identity morphism. -/
  ι_refl :
    {x : S} → ι (S.refl x) ≋ Setoid.Erased.Morphism.id (fibre x)

  /-- `ι (y ≈ x)` is a left-inverse for `ι (x ≈ y)`. -/
  ι_symm_compose :
    {x y : S}
    → (h : x ≈ y)
    → ι (S.symm h) ∘m ι h ≋ Setoid.Erased.Morphism.id'
  /-- `ι (y ≈ x)` is a right-inverse for `ι (x ≈ y)`. -/
  ι_compose_symm :
    {x y : S}
    → (h : x ≈ y)
    → ι h ∘m ι (S.symm h) ≋ Setoid.Erased.Morphism.id'

  /-- Transitive reindexing is the same as the composition of sub-reindexers. -/
  ι_trans :
    {x y z : S}
    → (hxy : x ≈ y)
    → (hyz : y ≈ z)
    → ι (S.trans hxy hyz) ≋ ι hxy ∘m ι hyz



/-- Morphisms between objects of `Setoid.Fam`. -/
structure Fam.Morphism
  {S₁ S₂ : Setoid.Erased}
  (F₁ : Fam S₁) (F₂ : Fam S₂)
where
  /-- Map `F₁`-indices to `F₂`-indices. -/
  indexMap : S₁ ⇒ S₂
  /-- Map `F₁`'s fibre to that of `F₂` (with appropriate indexing). -/
  fibreMap :
    (x : S₁)
    → (F₁.fibre x) ⇒ (F₂.fibre $ indexMap.map x)
  /-- Proof that re-indexing commutes with fibre mapping. -/
  ιMap :
    {x x' : S₁}
    → (h : x ≈ x')
    → (fibreMap x ∘m F₁.ι h) ≋ (F₂.ι $ indexMap.proper h) ∘m (fibreMap x')



/-- Category with families. -/
structure Cwf where
  base : Fam.Cat
  func : base.op → Setoid.Fam
