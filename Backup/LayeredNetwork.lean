-- Core/LayeredNetwork.lean
--
-- Layered Network Framework for M3P
-- Based on: "A Strongly Polynomial Algorithm for Membership in the
--            Pedigree Polytope" (Arthanari, Math. Prog. Series A)
--
-- All type definitions (LayeredPoint, ConvexWitness, RigidEntry,
-- LayeredNetwork, FATkFeasible, Commodity, MCFFeasible) live in
-- LayeredNetworkTypes.lean.
--
-- This file contains:
--   §6  Necessity direction (S_O, S_D, necessityFlow, necessity)
--   §7  Lemmas YsinMI and Ysinconv
--   §8  Sufficiency direction
--   §9  Main N&S theorem
--   §10 Sorry inventory

import MembershipProject.Core.LayeredNetworkTypes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace MembershipProject.Core

open Nat

-- ============================================================================
-- SECTION 6: NECESSITY DIRECTION
-- ============================================================================
--
-- Paper Theorem imptheorem (§6.2):
--   X/(k+1) ∈ conv(P_{k+1}) → MCF(k) has z* = z_max.
--
-- Proof engine: PartitionProbabilityFlowProblem.lean (Lemma 3).
-- f(e, e') = ∑_{r ∈ S_O(e) ∩ S_D(e')} λ_r
-- satisfies all flow constraints by prob_partition_is_feasible_flow.

/-- S_O(e): pedigrees in witness that use triple e at layer k.
    Paper §6: S_O(e) = { r ∈ I(λ) | X^r uses edge e at layer k }. -/
noncomputable def S_O {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X)
    (e : Triple) : Finset ℕ :=
  wit.idx.filter (fun r => e ∈ (wit.ped r).triangles)

/-- S_D(e'): pedigrees in witness that use triple e' at layer k+1.
    Paper §6: S_D(e') = { r ∈ I(λ) | X^r uses edge e' at layer k+1 }. -/
noncomputable def S_D {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X)
    (e' : Triple) : Finset ℕ :=
  wit.idx.filter (fun r => e' ∈ (wit.ped r).triangles)

/-- The necessity flow: f(e, e') = ∑_{r ∈ S_O(e) ∩ S_D(e')} λ_r.
    Paper Theorem imptheorem eq. (flowdef). -/
noncomputable def necessityFlow {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X)
    (e e' : Triple) : ℚ :=
  (S_O wit e ∩ S_D wit e').sum wit.weight

/-- Origin conservation: ∑_{e'} f(e, e') = ∑_{r ∈ S_O(e)} λ_r.
    Proof uses prob_origin_equals_sum_intersections. -/
lemma necessity_supply {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X)
    (e : Triple) (he : e ∈ Delta k) :
    (Delta (k + 1)).sum (fun e' => necessityFlow wit e e') =
    (S_O wit e).sum wit.weight := by
  sorry

/-- Sink conservation: ∑_e f(e, e') = ∑_{r ∈ S_D(e')} λ_r = x(e').
    Proof symmetric to necessity_supply. -/
lemma necessity_demand {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X)
    (e' : Triple) (he' : e' ∈ Delta (k + 1)) :
    (Delta k).sum (fun e => necessityFlow wit e e') =
    (S_D wit e').sum wit.weight := by
  sorry

/-- Supply from S_O(e) equals x(e). -/
lemma S_O_sum_eq_x {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X)
    (e : Triple) (he : e ∈ Delta k) :
    (S_O wit e).sum wit.weight = X.x e := by
  sorry

/-- Demand at S_D(e') equals x(e'). -/
lemma S_D_sum_eq_x {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X)
    (e' : Triple) (he' : e' ∈ Delta (k + 1)) :
    (S_D wit e').sum wit.weight = X.x e' := by
  sorry

/-- Rigid pedigree total outflow = μ_P.
    Paper Lemma extension_Lemma (§6.2):
    ∑_{r ∈ I(λ) ∩ EXT(P,k+1)} λ_r = μ_P.
    KEY (Issue 2): flow splits across multiple destinations. -/
lemma rigid_total_flow_eq_weight {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X)
    (net : LayeredNetwork n k)
    (P : RigidEntry n) (hP : P ∈ net.rigid) :
    (Delta (k + 1)).sum (fun e' =>
      (wit.idx.filter (fun r =>
        P.pedigree.triangles.toFinset ⊆
          (wit.ped r).triangles.toFinset ∧
        e' ∈ (wit.ped r).triangles)).sum wit.weight) = P.weight := by
  sorry

/-- Necessity: X/(k+1) ∈ conv(P_{k+1}) implies MCF(k) achieves z_max.
    Paper Theorem imptheorem, §6.2.
    Defined as noncomputable def since MCFFeasible is Type, not Prop. -/
noncomputable def necessity
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k)
    (wit : ConvexWitness n (k + 1) X) :
    MCFFeasible n k net X := by
  sorry

-- ============================================================================
-- SECTION 7: LEMMAS FOR SUFFICIENCY  (Paper §6.2)
-- ============================================================================

/-- Lemma YsinMI (paper §6.2):
    Given MCF(k) with z* = z_max, for each s ∈ S_k,
    (1/v^s) Y^s is MIR-feasible at level k. -/
lemma Y_s_in_PMI
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k)
    (mcf : MCFFeasible n k net X)
    (s   : Commodity n k)
    (hs  : s ∈ mcf.commodities) :
    ∃ F : MIRFeasible k, ∀ e : ℕ × ℕ, F.u 0 e ≤ 1 := by
  sorry

/-- Lemma Ysinconv (paper §6.2):
    Given MCF(k) with z* = z_max, for each s ∈ S_k,
    (1/v^s) Y^s / k ∈ conv(P_k). -/
lemma Y_s_in_conv
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k)
    (mcf : MCFFeasible n k net X)
    (s   : Commodity n k)
    (hs  : s ∈ mcf.commodities) :
    ∃ wit : ConvexWitness n k X,
      ∀ r ∈ wit.idx,
        (wit.ped r).triangles.getLast? = some s.src := by
  sorry

-- ============================================================================
-- SECTION 8: SUFFICIENCY DIRECTION  (Paper §6.2 Converse)
-- ============================================================================
--
-- MCF z* = z_max → X/(k+1) ∈ conv(P_{k+1})
--
-- Proof outline (paper):
--   1. For each s ∈ S_k, apply Y_s_in_conv → pedigrees ending in src(s)
--   2. Extend each P by tgt(s) to get P' ∈ P_{k+1}, weight = v^s · γ_P
--   3. Add rigid pedigrees R_k, each as pedigree in P_{k+1}
--   4. Total weight = ∑_s v^s + ∑_P μ_P = z_max + (1-z_max) = 1 ✓

/-- Sufficiency: MCF(k) achieves z_max → X/(k+1) ∈ conv(P_{k+1}).
    Paper: Converse of Theorem imptheorem, §6.2.
    Defined as noncomputable def since ConvexWitness is Type. -/
noncomputable def sufficiency
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k)
    (mcf : MCFFeasible n k net X) :
    Nonempty (ConvexWitness n (k + 1) X) := by
  sorry

-- ============================================================================
-- SECTION 9: THE MAIN N&S THEOREM  (Paper Theorem maintheorem, §6.2)
-- ============================================================================

/-- Main theorem: X/(k+1) ∈ conv(P_{k+1}) ↔ MCF(k) has z* = z_max.
    Paper Theorem maintheorem, §6.2. -/
theorem main_ns_theorem
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k) :
    Nonempty (ConvexWitness n (k + 1) X) ↔
    Nonempty (MCFFeasible n k net X) := by
  constructor
  · intro ⟨wit⟩
    exact ⟨necessity hk hkn X net wit⟩
  · intro ⟨mcf⟩
    exact sufficiency hk hkn X net mcf

-- ============================================================================
-- SECTION 10: SORRY INVENTORY
-- ============================================================================
--
-- [Sorry 1] necessity_supply
--   Use prob_origin_equals_sum_intersections with:
--     D = I(λ), D₁ = S_O partition, D₂ = S_D partition, p(r) = λ_r.
--
-- [Sorry 2] necessity_demand
--   Symmetric to necessity_supply, swap D₁ and D₂.
--
-- [Sorry 3] S_O_sum_eq_x
--   From wit.combo: rewrite ∑_{r ∈ S_O(e)} λ_r as wit.combo applied to e.
--
-- [Sorry 4] S_D_sum_eq_x
--   From wit.combo applied to e' at layer k+1.
--
-- [Sorry 5] rigid_total_flow_eq_weight
--   Paper Lemma extension_Lemma (§6.2): induction on k.
--   Closed by InstantFlow.lean instant_rigid_total + Lemma6.lean.
--
-- [Sorry 6] necessity
--   Construct MCFFeasible using necessityFlow as f_s.
--   Uses InstantFlow.lean (lemma_11_instant_flow_feasible) as engine.
--
-- [Sorry 7] Y_s_in_PMI
--   Paper Lemma YsinMI §6.2.
--   ∑_{e ∈ E_{l-1}} y^s_l(e) = v^s for l ∈ [4,k].
--   From MCF flow conservation at each layer for commodity s.
--
-- [Sorry 8] Y_s_in_conv
--   Paper Lemma Ysinconv §6.2. Induction on k.
--   Uses Y_s_in_PMI + restricted network argument.
--
-- [Sorry 9] sufficiency
--   Combine Y_s_in_conv for all s ∈ S_k.
--   Extend by tgt(s), combine with R_k.
--   Weight check: ∑_s v^s + ∑_P μ_P = z_max + (1-z_max) = 1.

end MembershipProject.Core
