import FilesAndNamespaces.Init
import FilesAndNamespaces.Data.Basics



-- currently inside the `_root_` namespace
namespace Lst
  -- currently inside `_root_.Lst`, and we `import`ed `FilesAndNamespaces.Data.Basics` so
  -- `Lst` is defined and visible. `Opt` comes from `Init.lean` in case you're wondering.
  def fold (init : β) (f : β → α → β) : Lst α → β
    | Lst.nil => init
    | head::tail => fold (f init head) f tail
namespace Lst
