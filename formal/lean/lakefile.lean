import Lake
open Lake DSL

package «narya-formal» where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.19.0"

@[default_target]
lean_lib NaryaFormal where
  roots := #[`NaryaFormal]
