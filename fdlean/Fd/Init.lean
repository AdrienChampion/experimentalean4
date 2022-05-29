/-!
# Basic Types and Helpers
-/



section NoMathlib
  --- Commutativity.
  @[simp, inline]
  def commutes (op : α → α → α) : Prop :=
    ∀ a₁ a₂,
      op a₁ a₂ = op a₂ a₁

  class Zero (α : Type u) :=
    zero : α
  instance : Zero Nat := ⟨0⟩
  instance : Zero Int := ⟨0⟩

  open Zero (zero)

  class One (α : Type u) :=
    one : α
  instance : One Nat := ⟨1⟩
  instance : One Int := ⟨1⟩

  open One (one)
end NoMathlib



section Range
  --- A range, inclusive on both ends.
  abbrev Range α := α × α

  infix:min "··" => (fun lb ub => ((lb, ub) : Range _))

  --- Conversion from regular products to ranges.
  instance : Coe (α × α) (Range α) where
    coe := id
  --- Conversion from ranges to regular products.
  instance : Coe (Range α) (α × α) where
    coe := id

  --- Length of a range.
  def Prod.len [Sub α] (self : Range α) : α :=
    self.1 - self.2

  --- `True` if the range is empty.
  def Prod.isEmpty [LT α] (self : Range α) : Prop :=
    self.2 < self.1
  --- `Prod.isEmpty` is decidable.
  instance
    [inst : LT α] [decLt : DecidableRel inst.lt]
    {self : Range α}
    : Decidable self.isEmpty
  :=
    by apply decLt
      

  --- Inclusive range over naturals.
  partial def Prod.fold
    (range : Range Int)
    (acc : α)
    (fld : α → Int → α)
    : α
  :=
    if range.1 ≤ range.2 then
      let acc := fld acc range.1
      let range := range.1 + 1 ·· range.2
      range.fold acc fld
    else
      acc
end Range



section Conv
  --- Total conversion from `src` to `tgt`.
  class Of (src: Type s) (tgt : Type t)where
    of : src → tgt
  
  postfix:55 " :>" => Of.of

  --- Conversion to self.
  instance : Of α α where
    of := id

  --- `OfNat → Of Nat`
  instance {conv : (n : Nat) → OfNat α n} : Of Nat α where
    of val :=
      conv val
      |>.ofNat

  --- `Of` is transitive.
  instance instTransOf [ofαβ : Of α β] [ofβγ : Of β γ] : Of α γ where
    of a :=
      ofαβ.of a
      |> ofβγ.of
end Conv



namespace Int
  /-!
# Lemmas for `Int`

`Int` is lacking in lemmas in that it has basically none.

The lemmas in this section are going to be useful 
  -/

  --- Addition is commutative.
  theorem add_comm :
    ∀ (i₁ i₂ : Int), i₁ + i₂ = i₂ + i₁
  := by
    intros i₁ i₂
    cases i₁
    <;> cases i₂
    <;> simp [HAdd.hAdd, Add.add, Int.add]
    <;> rw [Nat.add_comm]

  --- Multiplication is commutative.
  theorem mul_comm :
    ∀ (i₁ i₂ : Int), i₁ * i₂ = i₂ * i₁
  := by
    intros i₁ i₂
    cases i₁
    <;> cases i₂
    <;> simp [HMul.hMul, Mul.mul, Int.mul, Nat.mul_comm]
    <;> rw [Nat.mul_comm]

  --- Zero is left-neutral for `+`.
  theorem zero_add (i : Int) : 0 + i = i := by
      simp [HAdd.hAdd, Add.add, Int.add]
      cases i
      <;> simp [subNatNat]

  --- Zero is right-neutral for `+`.
  theorem add_zero (i : Int) : i + 0 = i := by
      rw [add_comm]
      exact zero_add i

  --- One is left-neutral for `*`.
  theorem one_mul (i : Int) : 1 * i = i := by
      simp [HMul.hMul, Mul.mul, Int.mul]
      cases i
      <;> simp [negOfNat]

  --- One is right-neutral for `*`.
  theorem mul_one (i : Int) : i * 1 = i := by
      rw [mul_comm]
      exact one_mul i
end Int

