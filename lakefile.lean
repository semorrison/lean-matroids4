import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

package «matroid» {
  -- add package configuration options here
}

lean_lib «Matroid» {
  -- add library configuration options here
}

lean_lib ForMathlib where
  roots := #[`ForMathlib]
