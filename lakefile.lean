import Lake
open Lake DSL

package RandomSystems where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0-rc1"

@[default_target]
lean_lib RandomSystems
