import Lake
open Lake DSL

package catExtendedEqIssue {
  -- add package configuration options here
}

lean_lib CatExtendedEqIssue {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe catExtendedEqIssue {
  root := `Main
}
