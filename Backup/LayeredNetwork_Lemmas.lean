-- Core/LayeredNetwork_Lemmas.lean
-- Supporting lemmas for the N&S theorem
-- Lemmas 6, 11, 12, 13 from the paper

import MembershipProject.Core.LayeredNetwork_DS
import MembershipProject.Core.PartitionProbabilityFlowProblem

namespace MembershipProject.Core

-- ============================================================================
-- LEMMA 6: Extension Lemma
-- ============================================================================

/-- Lemma 6: For any convex combination λ representing X/(k+1) and any
    rigid pedigree P ∈ R_{l-1}, the total weight of extensions of P in λ equals μ_P. -/
theorem lemma_6
    {n k l : ℕ} (hkl : l ≤ k)
    (X : LayeredPoint n) (hk : k + 1 ≤ n)
    (net : LayeredNetwork n k) (h_well_defined : net.well_defined)
    (λ : ConvexWitness n (k + 1) X)
    (P : RigidPedigree n (l - 1)) (hP : P ∈ net.rigid_at_layer (l - 1)) :
    (extensionsOf λ P).sum λ.weight = P.weight := by
  -- Proof by induction on w from l to k
  -- See paper Appendix for details
  sorry

-- ============================================================================
-- LEMMA 11: Instant flow is feasible for F_l
-- ============================================================================

/-- Lemma 11: Given Lemma 13, the instant flow for INST(λ, l) is feasible for F_l -/
lemma lemma_11
    {n k l : ℕ} (h : 4 ≤ l) (hlk : l ≤ k)
    (X : LayeredPoint n) (hk : k + 1 ≤ n)
    (net : LayeredNetwork n k) (h_well_defined : net.well_defined)
    (λ : ConvexWitness n (k + 1) X) :
    let λ_l := λ.restrict (by omega)
    let inst := INST λ_l h (by omega) (by omega)
    inst.is_feasible_for (F_l net) := by
  -- Uses Lemma 13 to ensure paths exist
  sorry

-- ============================================================================
-- LEMMA 12: Base case for k = 5
-- ============================================================================

/-- Lemma 12: For k = 5, every pedigree active for X/5 has its path available in N₄(L₅*) -/
lemma lemma_12
    {n : ℕ} (hn : 5 ≤ n)
    (X : LayeredPoint n) (hX : X ∈ P_MI(n))
    (net : LayeredNetwork n 4) (h_well_defined : net.well_defined)
    (λ : ConvexWitness n 5 X)
    (r : ℕ) (hr : r ∈ λ.idx) :
    let P := λ.ped r
    let e₄ := P.triangle_at 4
    let e₅ := P.triangle_at 5
    let L := (e₄, e₅)
    (P.restrict 4).path_available_in (net.restricted_network L) := by
  -- Proof by contradiction using deletion rules
  sorry

-- ============================================================================
-- LEMMA 13: Existence of Pedigree Paths (by induction)
-- ============================================================================

/-- Lemma 13: Every active pedigree for X/(k+1) satisfies that for 4 ≤ l ≤ k,
    either P/l is in R_{l-1} or path(P/l) is available in N_{l-1}(L_l*) -/
lemma lemma_13
    {n k l : ℕ} (h : 4 ≤ l) (hlk : l ≤ k)
    (X : LayeredPoint n) (hk : k + 1 ≤ n)
    (net : LayeredNetwork n k) (h_well_defined : net.well_defined)
    (λ : ConvexWitness n (k + 1) X)
    (r : ℕ) (hr : r ∈ λ.idx) :
    let P := λ.ped r
    let e_l := P.triangle_at l
    let e_{l+1} := P.triangle_at (l + 1)
    let L_l := (e_l, e_{l+1})
    (∃ (Q : RigidPedigree n (l - 1)), Q.ped = P.restrict (l - 1) ∧ Q ∈ net.rigid_at_layer (l - 1)) ∨
    (P.restrict l).path_available_in (net.restricted_network L_l) := by
  -- Induction on l using Lemma 12 as base case
  induction' l using Nat.le_induction with l IH
  · -- Base case l = 5
    left -- or right? Need to check paper
    sorry
  · -- Inductive step
    sorry

end MembershipProject.Core
