-- File No. 8 - N_MIRLemma.lean
--
-- The MI feasibility lemma and its consequences.
--
-- Problem MI(l) (arXiv paper, Chapter 3) in matrix form:
--   Minimise  C·X
--   subject to  E_{[l]} X = 1_{l-3}
--               A_{[l]} X + U^{(l)} = U^{(3)}
--               X ≥ 0,  U^{(l)} ≥ 0
--
-- Expanding recursively:  U^{l-1}(p) - A^{(l)} x_l(p) = U^{(l)}(p)
-- i.e.  u(m+1) p + x(m+4) p = u(m) p  (u_rec in MIRFeasible)
--
-- MIRFeasible_mk: constructor packaging the four MI conditions.
-- MIRFeasible_antitone: U^{m+4}(p) ≤ U^{m+3}(p) (the available slack
--   of edge (i,j) is non-increasing: each insertion can only reduce
--   the available slack, never increase it).
--
-- Reference: Arthanari, T.S. arXiv:2507.09069v1 [math.CO].

import MembershipProject.Core.N_Types

namespace MembershipProject.Core

-- ============================================================
-- MIRFeasible_mk: packages the four MI proof obligations
-- into a MIRFeasible structure.
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
-- MIRFeasible_antitone: u is non-increasing in m.
-- Proof: u(m) = u(m+1) + x(m+4) ≥ u(m+1) since x(m+4) ≥ 0.
-- The available slack of edge (i,j) can only decrease as l increases:
-- each insertion at layer l either uses edge (i,j) (reducing its slack)
-- or leaves it unchanged.
-- ============================================================

lemma MIRFeasible_antitone (n m : ℕ) (F : MIRFeasible n)
    (hm : m + 4 ≤ n) (p : ℕ × ℕ) :
    F.u (m + 1) p ≤ F.u m p := by
  have hrec := F.u_rec m hm p
  have hnn  := F.x_nn (m + 4) p
  linarith

end MembershipProject.Core
