import Lake
open Lake DSL

package category {
}
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib Category {
}

@[defaultTarget]
lean_exe category {
  root := `Main
}
