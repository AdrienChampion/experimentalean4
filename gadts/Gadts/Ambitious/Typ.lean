inductive Typ
| bool
| nat

abbrev Typ.type : Typ → Type
| .bool => Bool
| .nat => Nat

instance instCoeSortTypType : CoeSort Typ Type :=
  ⟨Typ.type⟩



class ToTyp (α : Type) where
  typ : Typ

instance instToTypBool : ToTyp Bool :=
  ⟨Typ.bool⟩
instance instToTypNat : ToTyp Nat :=
  ⟨Typ.nat⟩
