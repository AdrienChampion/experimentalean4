import Cat.Init



/-! # Introduces the notion of setoid with erased carrier
-/

namespace Cat



/-- Alias for Lean's `Setoid` class. -/
abbrev Zetoid :=
  Setoid


/-- Erases the carrier of a `Setoid`.

Instead of `Setoid α`, this structure stores `α` as `Carrier` alongside an instance of `Zetoid
Carrier`. This allows functions producing `Setoid`s to produce different carriers for different
input values.
-/
structure Setoid
where protected innerMk ::
  Carrier : Sort c
  instZetoid : Zetoid Carrier

/-- Notation `|S|` expanding to `S.Carrier`. -/
macro "| " t:term " |" : term =>
  `(Setoid.Carrier $t)



/-! ## Useful instances -/

-- /-- Allow using `S : Setoid` directly as `|S|`.

-- **DO NOT** abuse this, it can destroy readability.
-- -/
-- instance instCoeSortSetoidErased
-- : CoeSort Setoid.{c} (Sort c) where
--   coe :=
--     Setoid.Carrier

/-- Bring `S.instSetoid : Zetoid |S|` in scope whenever we handle `|S|`. -/
instance instSetoidSetoidErased
  {S : Setoid}
: Zetoid |S| :=
  S.instZetoid

/-- Give access to `α ≈ β` notation (`\~~`). -/
instance instHasEquivSetoidErased
  (S : Setoid)
: HasEquiv |S| :=
  @instHasEquiv S.Carrier S.instZetoid



/-! ## Operations over `Setoid` -/

namespace Setoid
  /-- Constructor. -/
  def mk
    (Carrier : Type c)
    [setoid : Zetoid Carrier]
  : Setoid :=
    ⟨Carrier, setoid⟩

  /-- Constructor from a carrier. -/
  def ofCarrier
    {M : Setoid}
    (_ : |M|)
  : Setoid :=
    M

  /-! ### Lift stuff from inner `Zetoid` instance -/

  variable
    (self : Setoid)

  def r :=
    self.instZetoid.r

  def refl :=
    self.instZetoid.refl
  def symm
    {a b : self.Carrier}
  : a ≈ b → b ≈ a :=
    self.instZetoid.symm
  def trans
    {a b c : self.Carrier}
  : a ≈ b → b ≈ c → a ≈ c:=
    self.instZetoid.trans
end Setoid
