import Lake
open Lake DSL

package cat {
  -- add package configuration options here
}

lean_lib Cat {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe cat {
  root := `Main
}
