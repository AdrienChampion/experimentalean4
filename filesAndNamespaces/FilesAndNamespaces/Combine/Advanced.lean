import FilesAndNamespaces.Combine.Basics
import FilesAndNamespaces.Data.Advanced



namespace Combine



--- Merges two string-able things.
def join [A : ToString α] [B : ToString β]
  (a : α) (b : β)
  : String
:=
  let a := A.toString a
  let b := B.toString b
  s! "{a}{b}"

--- Merges a list of string-able things.
def fold [A : ToString α]
  : Lst.Lst α → String
:=
  Lst.fold "" join
