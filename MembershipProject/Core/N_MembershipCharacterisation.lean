-- Core/N_MembershipCharacterisation.lean
--
-- The complete Necessary and Sufficient condition for membership
-- in the Pedigree Polytope conv(Pₙ).
--
-- This file completes the research agenda of Chapter 5:
--
--   X ∈ conv(Pₙ) ↔ MCF(n-1) has z* = z_max
--
-- Structure:
--   Sufficiency (←): proved in N_Sufficiency.lean (0 sorries).
--   Necessity   (→): stated as axiom necessity_of_mcf,
--                    citing Chapter 5 of Arthanari 2025 and
--                    Arthanari 2023 (Pedigree Polytopes, Springer Nature).
--                    Full Lean 4 proof: N_Necessity.lean (Backup folder,
--                    16 sorries remaining, ongoing work).
--
-- NOTE: main_ns_theorem is NOT required for the P=NP chain.
--       The P=NP chain uses sufficiency only (N_Sufficiency.lean).
--       This file stands as a self-contained record of the complete
--       membership characterisation result.
--
-- Reference: Arthanari, T.S. (2025). A strongly polynomial algorithm
--            for membership in the pedigree polytope. Preprint.
--            Theorem 7 (N&S condition).
-- Reference: Arthanari, T.S. (2023). Pedigree Polytopes.
--            Springer Nature, Singapore. Chapter 5.

import MembershipProject.Core.N_Sufficiency
import MembershipProject.Core.N_SupportConcepts

namespace MembershipProject.Core

set_option linter.unusedVariables false

-- ============================================================================
-- NECESSITY AXIOM
-- ============================================================================

/-- Necessity of MCF(k) for membership in conv(P_{k+1}).
    Chapter 5, Theorem 7 (necessity direction):
    If X/k+1 ∈ conv(P_{k+1}) (witnessed by a ConvexWitness),
    then MCF(k) is feasible with z* = z_max.

    Proof (Chapter 5, Arthanari 2025):
    Construct the instant flow f_a = ∑_{r ∈ I(λ), Xʳ ∥ a} λ_r.
    This satisfies all MCF(k) constraints:
    (1) Non-negativity: from λ_r > 0.
    (2) Flow conservation: each pedigree has exactly one triangle per layer.
    (3) Capacity bounds: from F_k feasibility and rigid pedigree construction.
    (4) z* = z_max: from ∑_s vˢ = 1 - ∑_{P ∈ Rk} μ_P = z_max.

    Full Lean 4 formalisation: N_Necessity.lean (Backup folder, 16 sorries).
    Reference: Arthanari 2025, Chapter 5. Arthanari 2023, Chapter 5. -/
axiom necessity_of_mcf
    {n k : ℕ} (hk : 5 ≤ k) (hkn : k + 1 ≤ n)
    (X    : LayeredPoint n)
    (hX   : ∀ l, 4 ≤ l → l ≤ k + 1 → (Delta l).sum X = 1)
    (hXnn : ∀ t, X t ≥ 0)
    (net  : LayeredNetwork n k)
    (wit  : ConvexWitness n (k + 1) X) :
    Nonempty (MCFFeasible n k net X)

-- ============================================================================
-- MAIN N&S THEOREM
-- ============================================================================

/-- Main Necessary and Sufficient Condition for Membership in conv(Pₙ).
    Chapter 5, Theorem 7 (Arthanari 2025):

      X ∈ conv(Pₙ) ↔ MCF(n-1) is feasible with z* = z_max.

    (←) Sufficiency: proved in N_Sufficiency.lean (0 sorries).
        If MCF(n-1) has z* = z_max, then X ∈ conv(Pₙ).
        Proof: construct ConvexWitness from MCF solution.

    (→) Necessity: axiom necessity_of_mcf (this file), citing Chapter 5.
        If X ∈ conv(Pₙ), then MCF(n-1) has z* = z_max.
        Proof via instant flow construction (N_Necessity.lean, Backup).

    This result establishes M3P as the key algorithmic problem whose
    polynomial-time solvability (Chapter 6) leads to P = NP (Chapter 7).

    Reference: Arthanari 2025, Theorem 7.
               Arthanari 2023, Chapter 5. -/
theorem main_ns_theorem
    {n : ℕ} (hn : 6 ≤ n)
    (X    : LayeredPoint n)
    (hX   : ∀ l, 4 ≤ l → l ≤ n → (Delta l).sum X = 1)
    (hXnn : ∀ t, X t ≥ 0)
    (net  : LayeredNetwork n (n - 1))
    (hzmax : 0 < zMax net) :
    Nonempty (ConvexWitness n n X) ↔
    Nonempty (MCFFeasible n (n - 1) net X) := by
  constructor
  · -- (→) Necessity: X ∈ conv(Pₙ) → MCF(n-1) feasible
    -- Axiom necessity_of_mcf, citing Chapter 5.
    -- Full proof: N_Necessity.lean (Backup folder, 16 sorries).
    intro ⟨wit⟩
    exact necessity_of_mcf (by omega) (by omega) X
      (fun l hl hle => hX l hl (by omega)) hXnn net (wit.cast (by omega))
  · -- (←) Sufficiency: MCF(n-1) feasible → X ∈ conv(Pₙ)
    -- Proved in N_Sufficiency.lean (0 sorries).
    intro ⟨mcf⟩
    have hk  : 4 ≤ n - 1 := by omega
    have hkn : n - 1 + 1 ≤ n := by omega
    obtain ⟨wit, _⟩ := sufficiency hk hkn X net hzmax mcf
    exact ⟨wit.cast (by omega)⟩

end MembershipProject.Core
