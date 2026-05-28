-- File No. 2 - N_Types.lean
-- Core types: MIRFeasible and ConvexCombo.
-- MIRFeasible formalises the MI (Multistage Insertion) feasibility
-- conditions for an n-city pedigree solution.
-- Reference: Arthanari, T.S. Pedigree Polytopes, Springer Nature, 2023.

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace MembershipProject.Core

/-- A MIR-feasible solution for n cities.

    In the MI formulation, the layered network flow has:
    - u m p : the flow variable U^{m+3} at position p : ℕ × ℕ
              (layer m+3, edge position p)
    - x m p : the insertion variable y_{m+4} at position p
              (vertex m+4 inserted at position p)

    The feasibility conditions are:
    - u_rec : flow conservation at each layer:
              U^{m+3}(p) = U^{m+4}(p) + y_{m+4}(p)
              i.e. u m p = u (m+1) p + x (m+4) p
    - x_nn  : insertion variables are non-negative
    - u_nn  : flow variables are non-negative
    - u0_le1: initial flow ≤ 1 (capacity constraint) -/
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
