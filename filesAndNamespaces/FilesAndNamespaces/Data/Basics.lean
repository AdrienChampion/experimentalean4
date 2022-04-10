import FilesAndNamespaces.Combine.Basics



-- currently adding to the library's top-level namespace `_root_`
namespace Lst
  -- currently adding to `_root_.Lst`
  inductive Lst (α : Type u) :=
    | nil : Lst α
    | cons : α → Lst α → Lst α

  -- make `nil` directly visible instead of `Lst.nil`
  export Lst (nil cons)
  -- define an infix notation for `Lst.cons`
  infixr:70 " :: " => Lst.cons
end Lst



instance StringToString : Combine.ToString String where
  toString s := s
