import Lake
open Lake DSL

package err {
  -- add package configuration options here
}

lean_lib Err {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe err {
  root := `Main
}
