import Lake
open Lake DSL

package membershipProject where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4"

-- Add doc-gen4 here to enable the documentation generator
meta if get_config? env = some "dev" then
  require «doc-gen4» from git "https://github.com/leanprover-community/doc-gen4" @ "main"

lean_lib MembershipProject where
  globs := #[.andSubmodules `MembershipProject]
