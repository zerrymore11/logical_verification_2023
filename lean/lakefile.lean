import Lake

open Lake DSL

package love

@[default_target]
lean_lib LoVe {
  roots := #[`LoVe]
  globs := #[Glob.submodules `LoVe]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"
-- require std from git "https://github.com/leanprover/std4" @ "v4.19.0-rc3"
-- require std from git "https://github.com/leanprover/std4" @ "f523fcb75db2b472cda7d94d6caa5d745b1a0c26"
