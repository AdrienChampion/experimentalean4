import Lake
open Lake DSL

package «stream2» {
  -- add package configuration options here
}

lean_lib «Stream2» {
  -- add library configuration options here
}

@[default_target]
lean_exe «stream2» {
  root := `Main
}
