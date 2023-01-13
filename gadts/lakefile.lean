import Lake
open Lake DSL

package «gadts» {
  -- add package configuration options here
}

lean_lib «Gadts» {
  -- add library configuration options here
}

@[default_target]
lean_exe «gadts» {
  root := `Main
}
