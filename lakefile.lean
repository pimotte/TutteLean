import Lake
open Lake DSL

package «TutteLean» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"145e6ba702be03cbd05635f29bca8f2c95622da7"

@[default_target]
lean_lib «TutteLean» {
  -- add any library configuration options here
}
