import Gadts.Ambitious.Bool
import Gadts.Ambitious.Nat



instance instExprTypSpecTyp (typ : Typ) : ExprTypSpec typ.type :=
  match typ with
  | .bool => instExprTypSpecBool
  | .nat => instExprTypSpecNat



namespace Typ
  variable
    (self : Typ)

  def Spec :=
    instExprTypSpecTyp self

  def ops :=
    self.Spec.op
  def injs :=
    self.Spec.inj
  def rels :=
    self.Spec.rel
end Typ
