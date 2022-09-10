import Lake
open Lake DSL

package cla {
  -- add package configuration options here
}

lean_lib Cla {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe cla {
  root := `Main
}
