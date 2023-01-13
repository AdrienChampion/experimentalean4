import Gadts.Ambitious.Spec



class ExprTypSpec (α : Type) where
  instToTyp : ToTyp α
  instToString : ToString α
  op : OpSpec
  inj : OpSpec
  rel : OpSpec

instance instToTypExprTypSpec [Self : ExprTypSpec α] : ToTyp α :=
  Self.instToTyp
instance instToStringExprTypSpec [Self : ExprTypSpec α] : ToString α :=
  Self.instToString

namespace ExprTypSpec
  variable
    {α : Type}
    [Self : ExprTypSpec α]

  def type :=
    Self.instToTyp.typ
end ExprTypSpec