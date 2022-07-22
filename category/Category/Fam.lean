/-! # Categories with families

- <https://pdf.sciencedirectassets.com/272990/1-s2.0-S1571066108X03287/1-s2.0-S1571066108000431/main.pdf?X-Amz-Security-Token=IQoJb3JpZ2luX2VjEPn%2F%2F%2F%2F%2F%2F%2F%2F%2F%2FwEaCXVzLWVhc3QtMSJIMEYCIQDwSF1X%2BYO%2F420uK0n0MdZTtNU2%2B%2FDo5ql0cunor%2BFRewIhAJ4XOqT8wx%2BZAzPu8FBv2G6tz6E5ZWwiCtxrMsi6X2UEKtIECEIQBRoMMDU5MDAzNTQ2ODY1IgzjK4CqLFqIrVFPCUEqrwTnJTrTfLOTaY9k3Ch6O%2FSImGgJi0F7lkZDHIiBdgbeEStN4CpfodcMLuTFCmYzXcmYuzmkP%2FPJnxyvNcn5JrRLnaMewDE%2B3%2FGVoeYkVwCPjztK2DGe%2FsPV0RAVIIAnpwxDlOlbkXGsC3e7COE%2FOSf5fAuKjTzfdm5McO5%2B3sYtD8RkZQfex%2F7LNtLzy038RVAk06%2BUItTzCnkyVda%2F3D%2FSD3H5bGhXAoqx4npAWasoFiE%2FdK2Mc1sR2ctPrnNyA64eBGiPWMqcUC%2F2XP2%2Fqm6oOhzZ2mF%2BLaB939%2FKlHQW7cNpEI9pUK6nzVnCpLqvzJ%2F28yTN6JIMzhGTfyjeCqzwslLEGcnztnYJJarabqJNVz6vP8ZtuzitgE8U1RXtoznNUEvsf6WkqIIxUXFun2BetbEPKYWo03%2BY8513iWFUMjwUYA8qzmRqaKelG7mpBt2ethZ32OwA3A1sAyoieEl5F2hL39yQ4ci7OECkHaSdtcqfv9WOyx5yJyvR1tFDEeElXG%2BfDqwITeFX3Y5HYgqpgQnIO2j08O%2BxDWtFFmeDjrUlRIg%2FUYy3%2BjhOV1vCIWDK5DE%2BHDthVC8OQwZJsR7izuC8mnrQ6Uip8h6g7x%2Bi5Xj8ynsw9TJyG8uxZunW9W76VA%2BFtpwJvnjjK9qz5V3Mvw6TFC1kkkSU9tXDxol4oit51j0Kn%2B6DdZMFZ8xSCiScFp%2FWSmQbwc7P8Gj0Lc1G49Ta4PeJys4OIpj804UnMI6h5JYGOqgB0sUc2k7f5s6CwiuPaUtFtjOnuJ92Xbnyngs9my9kt8IEJfzf4YlOKQGSEAnb%2BY20id7AQ%2B1yEKJOTghF5n3VuxZrFAgm1UApCYelVTZVWpIR%2F4BlEjqK7eQXfHQcakfsShNZmxZaTb38s7XuaILIUtqSMzs%2FsDbgKeFlGbvmeh%2F4fHBmurgsRrRpoB82YAxmUtNWLpGgDb5jUstx5BRTki1xjbosnJHY&X-Amz-Algorithm=AWS4-HMAC-SHA256&X-Amz-Date=20220721T093450Z&X-Amz-SignedHeaders=host&X-Amz-Expires=300&X-Amz-Credential=ASIAQ3PHCVTYXTXEDTIG%2F20220721%2Fus-east-1%2Fs3%2Faws4_request&X-Amz-Signature=0affbbdd57922b0f96e28892245af10f9be3110f02ece17d8480d74994213d13&hash=f9d87630690a224ca4dbf56150bcb6d37ee97e58789a530871c3952447d85a86&host=68042c943591013ac2b2430a89b270f6af2c76d8dfd086a07176afe7c76c2c61&pii=S1571066108000431&tid=spdf-50948ff5-19da-4bb3-875f-03d9091e3445&sid=346b3b469d82e94daf8b1476084c2ca4555fgxrqb&type=client&ua=5755035c0153545c50&rr=72e2f1695ae23bb0>
-/



section erased_setoid

  /-- Erases the carrier of a setoid.

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

    variable
      (self : Erased)

    /-! ### Lift stuff from inner `Setoid` instance -/

    def r :=
      self.setoid.r

    def refl :=
      self.setoid.refl

    def symm
      {a b : self.Carrier}
    : a ≈ b → b ≈ a :=
      self.setoid.symm
    def r.symm
      {self : Erased}
      {a b : self.Carrier}
    : a ≈ b → b ≈ a :=
      self.symm

    def trans
      {a b c : self.Carrier}
    : a ≈ b → b ≈ c → a ≈ c:=
      self.setoid.trans
    def r.trans
      {self : Erased}
      {a b c : self.Carrier}
    : a ≈ b → b ≈ c → a ≈ c :=
      self.setoid.trans
  end Setoid.Erased

end erased_setoid



/-- A simple category, basis for categories with families. -/
structure Fam.Cat where
  Object : Sort o

  /-- This returns `Setoid.Erased` to allow dependent, arbitrary carriers. -/
  Arrow :
    Object → Object → Setoid.Erased

  compose {α β γ : Object} :
    Arrow β γ → Arrow α β → Arrow α γ
  compose_assoc
    {α β γ δ : Object}
    (f : Arrow γ δ) (g : Arrow β γ) (h : Arrow α β)
  : compose f (compose g h)
  = compose (compose f g) h

  id {α : Object} :
    Arrow α α
  id_compose (f : Arrow α β) :
    compose id f = f
  compose_id (f : Arrow α β) :
    compose f id = f



/-- Notion of morphism over `Setoid.Erased` (`⇒`). -/
structure Setoid.Erased.Morphism (α β : Setoid.Erased) where
  map : α → β
  proper {a₁ a₂ : α} :
    a₁ = a₂ → map a₁ = map a₂

infix:min " ⇒ " => Setoid.Erased.Morphism

/-- Composition of two morphisms (`∘m`). -/
def Setoid.Erased.Morphism.compose
  (f : β ⇒ γ) (g : α ⇒ β)
: α ⇒ γ where
  map :=
    f.map ∘ g.map
  proper {a₁ a₂} h :=
    let subst :=
      g.proper h
    by simp [subst]

infix:40 " ∘m " => Setoid.Erased.Morphism.compose

/-- Explicit identity morphism. -/
def Setoid.Erased.Morphism.id (α : Setoid.Erased) : Morphism α α where
  map := (·)
  proper := (·)
/-- Implicit identity morphism. -/
abbrev Setoid.Erased.Morphism.id' {α : Setoid.Erased} :=
  id α

/-- Function extensionality, not sure this makes a lot of sense. -/
protected def Setoid.Erased.Morphism.funext
  {α β : Setoid.Erased}
  {m₁ m₂ : α ⇒ β}
  (h : ∀ (x : α), m₁.map x = m₂.map x)
: m₁.map = m₂.map :=
  funext (f₁ := m₁.map) (f₂ := m₂.map) h

/-- Extensional equality (`≋`). -/
abbrev Setoid.Erased.Morphism.exteq
  {α β : Setoid.Erased}
  (f g : α ⇒ β)
: Prop :=
  ∀ (a : α), f.map a ≈ g.map a

infix:min " ≋ " => Setoid.Erased.Morphism.exteq



/-- Family of setoids indexed by a given setoid `S`.

- `fibre`: indexes setoids by elements of `S`'s carrier;
- `ι`: reindexing function, maps `S`'s equivalence relation into morphisms over the indexed setoids.
-/
structure Setoid.Fam
  (S : Setoid.Erased)
where
  fibre : S → Setoid.Erased
  ι :
    {x x' : S} → (x ≈ x') → (fibre x' ⇒ fibre x)

  /-- `ι` of the same index yields the identity morphism. -/
  ι_refl :
    {x : S} → ι (S.refl x) ≋ Erased.Morphism.id (fibre x)

  /-- `ι (y ≈ x)` is a left-inverse for `ι (x ≈ y)`. -/
  ι_symm_compose :
    {x y : S}
    → (h : x ≈ y)
    → ι (S.symm h) ∘m ι h ≋ Erased.Morphism.id'
  /-- `ι (y ≈ x)` is a right-inverse for `ι (x ≈ y)`. -/
  ι_compose_symm :
    {x y : S}
    → (h : x ≈ y)
    → ι h ∘m ι (S.symm h) ≋ Erased.Morphism.id'

  /-- Transitive reindexing is the same as the composition of sub-reindexers. -/
  ι_trans :
    {x y z : S}
    → (hxy : x ≈ y)
    → (hyz : y ≈ z)
    → ι (S.trans hxy hyz) ≋ ι hxy ∘m ι hyz
