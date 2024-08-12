import Lake
open Lake DSL

package «TutteLean» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"0b653510d11af5633ea9db4a07b865c88e24256d"

@[default_target]
lean_lib «TutteLean» {
  -- add any library configuration options here
}
