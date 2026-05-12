import Lake
open Lake DSL

package membershipProject where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4"

lean_lib MembershipProject where
  globs := #[.andSubmodules `MembershipProject]
