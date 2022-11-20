import Lake
open Lake DSL

package byCalcIndent {
  -- add package configuration options here
}

lean_lib ByCalcIndent {
  -- add library configuration options here
}

@[default_target]
lean_exe byCalcIndent {
  root := `Main
}
