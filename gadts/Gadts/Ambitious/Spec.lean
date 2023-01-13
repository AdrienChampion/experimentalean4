import Gadts.Init
import Gadts.Ambitious.Typ



structure OpTypeSpec where
  type : Type
  instToString : ToString type

instance instToStringOpTypeSpec
  {Self : OpTypeSpec}
: ToString Self.type :=
  Self.instToString

def OpTypeSpec.empty : OpTypeSpec where
  type := Empty
  instToString := inferInstance



structure OpSpec where
  un : OpTypeSpec
  bin : OpTypeSpec
  many : OpTypeSpec
  many1 : OpTypeSpec
  many2 : OpTypeSpec

def OpSpec.empty : OpSpec :=
  ⟨.empty, .empty, .empty, .empty, .empty⟩

instance instToStringOpSpecUn
  {Self : OpSpec}
: ToString Self.un.type :=
  inferInstance
instance instToStringOpSpecBin
  {Self : OpSpec}
: ToString Self.bin.type :=
  inferInstance
instance instToStringOpSpecMany
  {Self : OpSpec}
: ToString Self.many.type :=
  inferInstance
instance instToStringOpSpecMany1
  {Self : OpSpec}
: ToString Self.many1.type :=
  inferInstance
instance instToStringOpSpecMany2
  {Self : OpSpec}
: ToString Self.many2.type :=
  inferInstance
