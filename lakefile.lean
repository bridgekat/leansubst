import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

package «leansubst» {
  -- add package configuration options here
}

lean_lib «Leansubst» {
  -- add library configuration options here
}

@[default_target]
lean_exe «leansubst» {
  root := `Main
}
