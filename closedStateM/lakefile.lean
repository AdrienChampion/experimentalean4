import Lake
open Lake DSL

package csm {
  -- add package configuration options here
}

lean_lib Csm {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe csm {
  root := `Main
}
