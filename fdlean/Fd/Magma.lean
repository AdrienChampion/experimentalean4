import Fd.Init

/-!
# Magma and Other Group-Like Structures

See [magma on wikipedia][magma]. In particular, see [classification by properties][details] for a
breakdown of group-like structures, some of which will appear below.

We avoid mentioning associativity as a desperate attempt to include `Float`s, which have
non-commutative addition/multiplication. However, these operations are **supposed to be**
commutative: most *standards* do require commutativity, but some *implementations* don't actually
respect that. See Ariane 5's crash for instance (I think).

[magma]: https://en.wikipedia.org/wiki/Magma_(algebra)
[details]: https://en.wikipedia.org/wiki/Magma_(algebra)#Classification_by_properties
-/


--- A *magma* is just an `α`-closed operation `law`.
class Magma (α : Type u) where
  law : α → α → α

open Magma (law)

infix:65 " ·ₘ " => law



section AddMagma
  --- Addition magma.
  class AddMagma (α : Type u)
  extends HAdd α α α

  infix:65 " +ₘ " => AddMagma.law

  --- `Add → AddMagma`
  @[simp, inline]
  instance Add_to_AddMagma [HAdd α α α] : AddMagma α :=
    {}

  --- `AddMagma → Magma`
  @[simp, inline]
  instance AddMagma_to_Magma [inst : AddMagma α] : Magma α where
    law := inst.hAdd

  example : AddMagma Nat :=
    inferInstance
  example : Magma Nat :=
    inferInstance
  example : AddMagma Int :=
    inferInstance
  example : Magma Int :=
    inferInstance
end AddMagma



section MulMagma
  --- Multiplication magma.
  class MulMagma (α : Type u)
  extends HMul α α α

  infix:70 " *ₘ " => MulMagma.law

  --- `Mul → MulMagma`
  @[simp, inline]
  instance Mul_to_MulMagma [HMul α α α] : MulMagma α :=
    {}

  --- `MulMagma → Magma`
  @[simp, inline]
  instance MulMagma_to_Magma [inst : MulMagma α] : Magma α where
    law := inst.hMul

  example : MulMagma Nat :=
    inferInstance
  example : Magma Nat :=
    inferInstance
  example : MulMagma Int :=
    inferInstance
  example : Magma Int :=
    inferInstance
end MulMagma



section UMagma
  --- A *unital magma* is a `Magma` with a unit element.
  class Magma.Unital (α : Type u)
  extends
    Magma α
  where
    unitElm : α
    unit_left :
      ∀ (a : α), unitElm ·ₘ a = a
    unit_right :
      ∀ (a : α), a ·ₘ unitElm = a

  notation "unitₘ" => Magma.Unital.unitElm
  notation "<0>" => unitₘ
  notation "<1>" => unitₘ



  class Magma.AddUnital (α : Type u)
  extends
    AddMagma α,
    Zero α
  where
    zero_add :
      ∀ a, zero + a = a
    add_zero :
      ∀ a, a + zero = a
  
  --- `AddUnital → Unital`.
  instance [M : Magma.AddUnital α] : Magma.Unital α where
    unitElm :=
      M.zero
    unit_left :=
      M.zero_add
    unit_right :=
      M.add_zero



  class Magma.MulUnital (α : Type u)
  extends
    MulMagma α,
    One α
  where
    one_mul :
      ∀ a, one * a = a
    mul_one :
      ∀ a, a * one = a
  
  --- `MulUnital → Unital`.
  instance [M : Magma.MulUnital α] : Magma.Unital α where
    unitElm :=
      M.one
    unit_left :=
      M.one_mul
    unit_right :=
      M.mul_one



  instance instUnitalZeroNat : Magma.AddUnital Nat :=
    ⟨Nat.zero_add, Nat.add_zero⟩

  instance instUnitalOneNat : Magma.MulUnital Nat :=
    ⟨Nat.one_mul, Nat.mul_one⟩

  instance instUnitalZeroInt : Magma.AddUnital Int :=
    ⟨Int.zero_add, Int.add_zero⟩

  instance instUnitalOneInt : Magma.MulUnital Int :=
    ⟨Int.one_mul, Int.mul_one⟩
end UMagma



section Comm
  --- A *commutative unital magma* is a `Magma.Unital` with a commutative law.
  ---
  --- Just called `Comm` and not, say, `CommUnital` for brievety.
  class Magma.Comm (α : Type u)
  extends
    Unital α
  where
    comm : commutes law


  class Magma.AddComm (α : Type u)
  extends
    AddUnital α
  where
    comm : commutes toAddUnital.hAdd
  
  --- `AddComm → Comm`
  instance [inst : Magma.AddComm α] : Magma.Comm α :=
    ⟨inst.comm⟩


  class Magma.MulComm (α : Type u)
  extends
    MulUnital α
  where
    comm : commutes toMulUnital.hMul
  
  --- `MulComm → Comm`
  instance [inst : Magma.MulComm α] : Magma.Comm α :=
    ⟨inst.comm⟩



  instance instNatAddCommMagma : Magma.AddComm Nat where
    comm :=
      Nat.add_comm

  instance instNatMulCommMagma : Magma.MulComm Nat where
    comm :=
      Nat.mul_comm

  instance instIntAddCommMagma : Magma.AddComm Int where
    comm :=
      Int.add_comm

  instance instIntMulCommMagma : Magma.MulComm Int where
    comm :=
      Int.mul_comm
end Comm
