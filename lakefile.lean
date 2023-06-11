import Lake
open Lake DSL

-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4"

require std4 from git
  "https://github.com/leanprover/std4"@"d5471b83378e8ace4845f9a029af92f8b0cf10cb"

package «leansubst» {
  -- add package configuration options here
}

lean_lib «Leansubst» {
  -- add library configuration options here
}
