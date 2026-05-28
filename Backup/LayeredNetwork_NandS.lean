-- Core/LayeredNetwork_NandS.lean
-- Necessary and Sufficient Condition for Membership in Pedigree Polytope
-- Based on Theorem 7 from "A Strongly Polynomial Algorithm for Membership in the Pedigree Polytope" by T. Arthanari

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import MembershipProject.Core.LayeredNetwork  -- Contains working necessity theorem
import MembershipProject.Core.PartitionProbabilityFlowProblem
import MembershipProject.Core.LayeredNetwork_Lemmas  -- Will contain Lemmas 6, 11, 12, 13

namespace MembershipProject.Core

open Nat
open Finset
open BigOperators

-- ============================================================================
-- SECTION 14: LEMMAS FOR SUFFICIENCY (Paper Section 6.2)
-- ============================================================================

/-- Lemma YsinMI: From a commodity flow, we can construct a MIR-feasible solution.
    This corresponds to Lemma 7 in the paper. -/
lemma Y_s_in_PMI
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k)
    (mcf : MCFFeasible n k net X)
    (s   : Commodity n k)
    (hs  : s ∈ mcf.commodities) :
    ∃ F : MIRFeasible k, ∀ e : ℕ × ℕ, F.u 0 e ≤ 1 := by
  -- Following Lemma 7 in the paper
  -- Use commodityVector to construct Y^s (Equation 33)
  let Y := commodityVector s (mcf.f_s s) net

  -- Show that (1/v^s)Y^s satisfies MIR constraints
  -- This uses flow conservation properties from mcf
  sorry

/-- Lemma Ysinconv: From a commodity flow, we can construct a convex witness.
    This corresponds to Lemma 8/9 in the paper. -/
lemma Y_s_in_conv
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k)
    (mcf : MCFFeasible n k net X)
    (s   : Commodity n k)
    (hs  : s ∈ mcf.commodities) :
    ∃ wit : ConvexWitness n k X,
      ∀ r ∈ wit.idx, (wit.ped r).triangles.getLast? = some s.src := by
  -- Get MIR-feasible solution from Lemma 7
  obtain ⟨F, hF⟩ := Y_s_in_PMI hk hkn X net mcf s hs

  -- Decompose F as convex combination of extreme points (pedigrees)
  -- This uses the fact that extreme points of P_MI(k) are pedigrees

  -- Last component condition follows from commodity structure
  -- s.src is the unique node at layer k that the commodity flows through
  sorry

-- ============================================================================
-- SECTION 15: SUFFICIENCY DIRECTION (Paper Theorem 6)
-- ============================================================================

/-- Sufficiency: MCF(k) achieves z_max implies X/(k+1) ∈ conv(P_{k+1}).
    This is Theorem 6 in the paper. -/
theorem sufficiency
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k)
    (mcf : MCFFeasible n k net X) :
    ∃ wit : ConvexWitness n (k + 1) X, True := by
  -- Step 1: For each commodity, get convex witness using Lemma 8/9
  let commodities := mcf.commodities

  -- For each commodity s, we get a witness for X/k
  have for_each_s : ∀ s ∈ commodities,
      ∃ wit_s : ConvexWitness n k X,
        ∀ r ∈ wit_s.idx, (wit_s.ped r).triangles.getLast? = some s.src :=
    fun s hs => Y_s_in_conv hk hkn X net mcf s hs

  -- Choose such witnesses
  choose wit_s h_last using for_each_s

  -- Step 2: Extend each witness using the commodity's target
  let extended (s : Commodity n k) (wit : ConvexWitness n k X) :
      ConvexWitness n (k + 1) X :=
    { idx := wit.idx
      ped := fun r => (wit.ped r).extend s.tgt
        (by -- Prove that s.tgt is a valid extension
            -- Need to show s.tgt has a generator in wit.ped r
            -- This follows from arc_valid and flow conservation
            sorry)
      weight := fun r => (mcf.flow_vals s hs).symm ▸ s.flow_val * wit.weight r
      wt_pos := by
        intro r hr
        have h1 : s.flow_val > 0 := s.flow_pos
        have h2 : wit.weight r > 0 := wit.wt_pos r hr
        positivity
      wt_sum := by
        -- Sum of weights = s.flow_val * (sum of wit.weight) = s.flow_val * 1 = s.flow_val
        simp [mul_sum]
        rw [wit.wt_sum, mul_one]
      combo := by
        intro t ht
        -- Need to show combination property
        -- Cases: t.k ≤ k and t.k = k+1
        sorry }

  -- Step 3: Combine with rigid pedigrees from R_k
  -- Each rigid pedigree P in net.rigid_at_layer k has weight μ_P
  let rigid_witness : ConvexWitness n (k + 1) X :=
    { idx := (Finset.range net.rigid.length)
      ped := fun i => (net.rigid.get i).pedigree
      weight := fun i => (net.rigid.get i).weight
      wt_pos := by
        intro i hi
        simp at hi
        have := (net.rigid.get i).wt_pos
        exact this
      wt_sum := by
        -- Sum of rigid weights = 1 - z_max
        rw [← net.z_max_eq, ← mcf.total_flow]
        sorry
      combo := by
        -- Each rigid pedigree contributes to X/(k+1)
        -- This follows from construction of R_k
        sorry }

  -- Step 4: Combine all witnesses
  -- The final witness is the convex combination of:
  -- - For each commodity s, the extended witness with weight s.flow_val
  -- - For each rigid pedigree P, the rigid witness with weight μ_P
  -- Total weights sum to (∑ s.flow_val) + (∑ μ_P) = z_max + (1 - z_max) = 1

  -- This gives X/(k+1) as a convex combination of pedigrees
  sorry

-- ============================================================================
-- SECTION 16: THE MAIN N&S THEOREM (Paper Theorem 7)
-- ============================================================================

/-- Main theorem: necessary and sufficient condition for membership.
    This is Theorem 7 in the paper. -/
theorem main_ns_theorem
    {n : ℕ} (hn : n > 5)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n (n - 1))
    (hMIR : ∃ F : MIRFeasible n, True)
    (hprev : ∃ wit : ConvexWitness n (n - 1) X, True) :
    (∃ wit : ConvexWitness n n X, True) ↔
    Nonempty (MCFFeasible n (n - 1) net X) := by
  constructor
  · -- Necessity direction - import from LayeredNetworkDS
    intro ⟨wit, _⟩
    have hk : 4 ≤ n - 1 := by omega
    have hkn : n - 1 + 1 ≤ n := by omega
    have h_eq : n = (n - 1) + 1 := by omega

    -- Use the necessity theorem from LayeredNetworkDS
    -- Note: This theorem is proven and working in the original file
    exact LayeredNetworkDS.necessity hk hkn X net (wit.cast h_eq)

  · -- Sufficiency direction - using Theorem 6 above
    intro ⟨mcf⟩
    have hk : 4 ≤ n - 1 := by omega
    have hkn : n - 1 + 1 ≤ n := by omega
    obtain ⟨wit, _⟩ := sufficiency hk hkn X net mcf
    have h_eq : (n - 1) + 1 = n := by omega
    exact ⟨wit.cast h_eq, trivial⟩

end MembershipProject.Core
