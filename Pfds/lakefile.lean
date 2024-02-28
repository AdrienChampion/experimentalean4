import Lake
open Lake DSL

package «Pfds» where
  -- add package configuration options here

lean_lib «Pfds» where
  -- add library configuration options here

require std from git
  "https://github.com/leanprover/std4" @ "stable"

@[default_target]
lean_exe «pfds» where
  root := `Main
