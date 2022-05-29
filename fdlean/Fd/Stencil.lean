import Fd.Init
import Fd.Magma



class Carrier where
  ℕ : Type n
  instInhabitedℕ : Inhabited ℕ
  instAddMagmaℕ : Magma.AddComm ℕ
  instMulMagmaℕ : Magma.MulComm ℕ

  ℤ : Type z
  instInhabitedℤ : Inhabited ℤ
  instSubℤ : HSub ℤ ℤ ℤ
  instAddMagmaℤ : Magma.AddComm ℤ
  instMulMagmaℤ : Magma.MulComm ℤ

  instOfℕℤ : Of ℕ ℤ

  ℝ : Type r
  instInhabitedℝ : Inhabited ℝ
  instAddMagmaℝ : Magma.AddComm ℝ
  instMulMagmaℝ : Magma.MulComm ℝ

  instOfℤℝ : Of ℤ ℝ

  instOfℕℝ : Of ℕ ℝ :=
    -- default value, can be replaced by a direct conversion on instantiation for efficiency
    instTransOf (ofαβ := instOfℕℤ) (ofβγ := instOfℤℝ)



namespace Carrier
  def ℤ.of [C : Carrier] (n : ℕ) : ℤ :=
    C.instOfℕℤ.of n

  def ℝ.of [C : Carrier] (n : ℤ) : ℝ :=
    C.instOfℤℝ.of n

  def ℝ.ofℕ [C : Carrier] (n : ℕ) : ℝ :=
    C.instOfℕℝ.of n

  def ℕ.zero [C : Carrier] : ℕ :=
    C.instAddMagmaℕ.zero

  def ℕ.one [C : Carrier] : ℕ :=
    C.instMulMagmaℕ.one

  def ℤ.zero [C : Carrier] : ℤ :=
    C.instAddMagmaℤ.zero

  def ℤ.one [C : Carrier] : ℤ :=
    C.instMulMagmaℤ.one

  def ℝ.zero [C : Carrier] : ℝ :=
    C.instAddMagmaℝ.zero

  def ℝ.one [C : Carrier] : ℝ :=
    C.instMulMagmaℝ.one
end Carrier



namespace Carrier.Insts
  /-!
# Carrier Instances

Open this namespace to bring all instances in a `Carrier` in scope, allowing typeclass inference to
find them.
  -/

  instance [Carrier] : HAdd ℕ ℕ ℕ :=
    instAddMagmaℕ.toHAdd
  instance [Carrier] : HMul ℕ ℕ ℕ :=
    instMulMagmaℕ.toHMul

  instance [Carrier] : HAdd ℤ ℤ ℤ :=
    instAddMagmaℤ.toHAdd
  instance [Carrier] : HMul ℤ ℤ ℤ :=
    instMulMagmaℤ.toHMul
  instance [Carrier] : HSub ℤ ℤ ℤ :=
    instSubℤ

  instance [Carrier] : HAdd ℝ ℝ ℝ :=
    instAddMagmaℝ.toHAdd
  instance [Carrier] : HMul ℝ ℝ ℝ :=
    instMulMagmaℝ.toHMul
end Carrier.Insts



--- Bring instances and nat/int/real fields in scope.
open Carrier.Insts
open Carrier (ℕ ℤ ℝ)



structure Stencil [Carrier] where
  stencil : (ℝ → ℝ) → ℝ → ℝ → ℝ
  size : ℕ
  coef : ℤ → ℝ

def Stencil.sizeℤ [Carrier] (self : Stencil) : ℤ :=
  ℤ.of self.size

def Stencil.apply
  [C : Carrier]
  (self : Stencil)
  (u : ℝ → ℝ) (x : ℝ) (Δx : ℝ)
  : ℝ
:=
  let n := self.sizeℤ
  let lbound :=
    ℤ.zero - n
  let ubound :=
    n + ℤ.one
  by
    sorry
--   (lbound ·· ubound).fold
--     ℝ.zero
--     fun acc m =>
--       acc + (self.coef m) * u (x + (C.ofInt m) * Δx)



-- namespace ThisMakesNoSense

--   @[defaultInstance]
--   instance intCarrier : Carrier Int where
--     zeℝo := 0
--     ofInt := id
  
--   def stencil : Stencil Int where
--     stencil (map : Int → Int) (s₁ s₂ : Int) := map s₁ + map s₂
--     size := 3 -- whatever
--     coef := id

--   #eval stencil.apply id 7 8

-- end ThisMakesNoSense