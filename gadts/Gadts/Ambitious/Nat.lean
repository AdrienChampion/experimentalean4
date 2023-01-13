import Gadts.Init
import Gadts.Ambitious.ExprTypSpec



namespace Na1

namespace Op
  inductive Un
    | uMinus
  def Un.toString : Un → String
    | .uMinus => "-"
  instance : ToString Un :=
    ⟨Un.toString⟩

  def Un.Spec : OpTypeSpec where
    type := Un
    instToString := inferInstance



  inductive Bin
    | div
  def Bin.toString : Bin → String
    | .div => "/"
  instance : ToString Bin :=
    ⟨Bin.toString⟩

  def Bin.Spec : OpTypeSpec where
    type := Bin
    instToString := inferInstance



  inductive Many2
    | add
    | mul
  def Many2.toString : Many2 → String
    | .add => "+"
    | .mul => "*"
  instance : ToString Many2 :=
    ⟨Many2.toString⟩

  def Many2.Spec : OpTypeSpec where
    type := Many2
    instToString := inferInstance



  def Spec : OpSpec where
    un := Un.Spec
    bin := Bin.Spec
    many := .empty
    many1 := .empty
    many2 := Many2.Spec
end Op

def Inj.Spec : OpSpec :=
  .empty

namespace Rel

  inductive Many2
    | le
    | lt
  def Many2.toString : Many2 → String
    | .le => "≤"
    | .lt => "<"
  instance : ToString Many2 :=
    ⟨Many2.toString⟩
  
  def Many2.Spec : OpTypeSpec where
    type := Many2
    instToString := inferInstance

  def Spec : OpSpec where
    un := .empty
    bin := .empty
    many := .empty
    many1 := .empty
    many2 := Many2.Spec
end Rel

end Na1

instance instExprTypSpecNat : ExprTypSpec Nat where
  instToTyp := inferInstance
  instToString := inferInstance
  op := Na1.Op.Spec
  inj := Na1.Inj.Spec
  rel := Na1.Rel.Spec
