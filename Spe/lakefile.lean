import Lake
open Lake DSL

package spe {
  -- add package configuration options here
}

lean_lib Spe {
  -- add library configuration options here
}

@[default_target]
lean_exe spe {
  root := `Main
}
