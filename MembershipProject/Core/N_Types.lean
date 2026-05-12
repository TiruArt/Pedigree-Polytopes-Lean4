-- Core/N_Types.lean
-- MIRFeasible and ConvexCombo — now using Triple = ℕ × ℕ × ℕ.
-- MIRFeasible.u and .x indexed by ℕ × ℕ (position), unchanged.

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace MembershipProject.Core

/-- A MIR-feasible solution for n cities.
    u m p = U^(m+3) at position p : ℕ × ℕ
    x m p = y_{m+4} at position p
    u_rec : U^(m+1)(p) + x(m+4)(p) = U^(m)(p)  -/
structure MIRFeasible (n : ℕ) where
  u      : ℕ → ℕ × ℕ → ℚ
  x      : ℕ → ℕ × ℕ → ℚ
  h_n    : 4 ≤ n
  u_rec  : ∀ m, m + 4 ≤ n → ∀ p : ℕ × ℕ, u (m + 1) p + x (m + 4) p = u m p
  x_nn   : ∀ m p, 0 ≤ x m p
  u_nn   : ∀ m p, 0 ≤ u m p
  u0_le1 : ∀ p, u 0 p ≤ 1

/-- A convex combination of pedigrees. -/
structure ConvexCombo (k : ℕ) where
  idx      : Finset ℕ
  weight   : ℕ → ℚ
  h_nonneg : ∀ r ∈ idx, 0 ≤ weight r
  h_sum    : idx.sum weight = 1
  pos      : ∀ r ∈ idx, 0 < weight r

end MembershipProject.Core
