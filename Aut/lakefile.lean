import Lake
open Lake DSL

package «aut» {
  -- add package configuration options here
}

lean_lib «Aut» {
  -- add library configuration options here
}

@[default_target]
lean_exe «aut» {
  root := `Main
}
