-- Core/N_MIRLemma.lean
-- The reformulated MIR lemma (Lemma "obvious", Chapter 5):
--
-- Y ∈ P_MI(n) iff there exist slack u and y-values x satisfying:
--   (u_rec)  u(m+1) p + x(m+4) p = u(m) p
--   (x_nn)   x(m) p ≥ 0
--   (u_nn)   u(m) p ≥ 0
--   (u0_le1) u(0) p ≤ 1
-- This is exactly MIRFeasible n.
-- MIRFeasible_mk packages the four obligations.
-- MIRFeasible_antitone is a free consequence.

import MembershipProject.Core.N_Types

namespace MembershipProject.Core

-- ============================================================
-- MIRFeasible_mk: packages the four proof obligations
-- ============================================================

noncomputable def MIRFeasible_mk
    (n    : ℕ)
    (hn   : 4 ≤ n)
    (u    : ℕ → ℕ × ℕ → ℚ)
    (x    : ℕ → ℕ × ℕ → ℚ)
    (hrec : ∀ m, m + 4 ≤ n → ∀ p : ℕ × ℕ, u (m + 1) p + x (m + 4) p = u m p)
    (hxnn : ∀ m p, 0 ≤ x m p)
    (hunn : ∀ m p, 0 ≤ u m p)
    (hu0  : ∀ p, u 0 p ≤ 1) :
    MIRFeasible n where
  u      := u
  x      := x
  h_n    := hn
  u_rec  := hrec
  x_nn   := hxnn
  u_nn   := hunn
  u0_le1 := hu0

-- ============================================================
-- u is antitone when x ≥ 0: u(m+1) p ≤ u(m) p
-- ============================================================

lemma MIRFeasible_antitone (n m : ℕ) (F : MIRFeasible n) (hm : m + 4 ≤ n) (p : ℕ × ℕ) :
    F.u (m + 1) p ≤ F.u m p := by
  have hrec := F.u_rec m hm p
  have hnn  := F.x_nn (m + 4) p
  linarith

end MembershipProject.Core
