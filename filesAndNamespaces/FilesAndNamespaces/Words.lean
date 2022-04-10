import FilesAndNamespaces.Data
import FilesAndNamespaces.Combine



namespace Hello
  open Lst
  private def word : Lst.Lst String := "l"::"i"::"f"::"e"::nil

  def sayIt : String := Combine.fold word
end Hello

namespace World
  open Lst
  private def word := "s"::"u"::"x"::nil

  def sayIt : String := Combine.fold word
end World
