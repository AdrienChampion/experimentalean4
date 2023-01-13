import Gadts.Init
import Gadts.Ambitious.ExprTypSpec



namespace Boo1

namespace Op
  inductive Un
    | neg
  def Un.toString : Un → String
    | .neg => "¬"
  instance : ToString Un :=
    ⟨Un.toString⟩

  def Un.Spec : OpTypeSpec where
    type := Un
    instToString := inferInstance



  inductive Bin
    | conj
    | disj
  def Bin.toString : Bin → String
    | .conj => "∧"
    | .disj => "∨"
  instance : ToString Bin :=
    ⟨Bin.toString⟩

  def Bin.Spec : OpTypeSpec where
    type := Bin
    instToString := inferInstance



  def Spec : OpSpec where
    un := Un.Spec
    bin := Bin.Spec
    many := .empty
    many1 := .empty
    many2 := .empty
end Op

def Inj.Spec : OpSpec :=
  .empty

def Rel.Spec : OpSpec :=
  .empty

end Boo1

instance instExprTypSpecBool : ExprTypSpec Bool where
  instToTyp := inferInstance
  instToString := inferInstance
  op := Boo1.Op.Spec
  inj := Boo1.Inj.Spec
  rel := Boo1.Rel.Spec