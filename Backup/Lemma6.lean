-- Core/Lemma6.lean
-- ========================================================
-- Lemma 6: Extension Lemma
-- Paper: "A Strongly Polynomial Algorithm for Membership
--        in the Pedigree Polytope" by Tiru Arthanari
-- Section 6.2, pages 25-26
-- ========================================================

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import MembershipProject.Core.PedigreeDefinition
import MembershipProject.Core.LayeredNetwork
import MembershipProject.Core.InstantFlow        -- Lemma 11
import MembershipProject.Core.PartitionProbabilityFlowProblem  -- Lemma 3

namespace MembershipProject.Core

open Finset BigOperators

variable {n k l : ℕ} (hkl : l ≤ k) (hk : k + 1 ≤ n)
variable (X : LayeredPoint n) (net : LayeredNetwork n k) (h_well_defined : net.well_defined)
variable (λ : ConvexWitness n (k + 1) X)
variable (P : RigidPedigree n (l - 1)) (hP : P ∈ net.rigid_at_layer l)

/-- Definition of EXT(P, k) - pedigrees extending P to layer k -/
def EXT (P : Pedigree l) (k : ℕ) : Finset (Pedigree k) :=
  { Q : Pedigree k | Q.restrict l = P }

/-- Lemma 6: Extension Lemma -/
theorem extension_lemma :
    ∑ r ∈ λ.idx.filter (fun r => (λ.ped r) ∈ EXT P (k + 1)), λ.weight r =
    net.μ_weight P := by

  induction' k using Nat.le_induction with k IH

  case base =>
    -- Base case: k = l
    have hk_eq_l : k = l := by omega

    -- Get instant flow for layer l-1
    obtain ⟨inst, h_origin_cons, h_sink_cons, h_nonneg_flow, h_forbidden⟩ :=
      lemma_11_instant_flow_feasible X net λ (l-1) (by omega)

    -- P corresponds to origin e_prev in this flow
    let e_prev := P.edge_at_layer (l-1)

    -- Flow out of P equals sum of extensions
    have h_outflow : ∑ e' ∈ inst.destinations, inst.instant_flow e_prev e' =
        ∑ r ∈ λ.idx.filter (fun r => (λ.ped r).at_layer (l-1) = e_prev), λ.weight r := by
      rw [inst.h_instant_flow_def]
      simp [Finset.sum_filter, Finset.sum_comm]

    -- By feasibility, outflow = supply
    have h_supply : ∑ e' ∈ inst.destinations, inst.instant_flow e_prev e' = inst.supply e_prev :=
      h_origin_cons e_prev (by simp [inst.h_origins_eq]; exact P.edge_pos)

    -- Supply of P is μ_P (by rigidity)
    have h_supply_eq_μ : inst.supply e_prev = net.μ_weight P := by
      rw [inst.h_supply_eq e_prev]
      -- Only extensions of P can have e_prev at layer l-1
      apply Finset.sum_congr rfl
      intro r hr
      have h_extends : (λ.ped r).restrict (l-1) = P.pedigree :=
        rigid_determines_extension P hP (λ.ped r) hr.1 hr.2
      rfl

    -- Connect the two filter conditions
    have h_eq_filters :
        (λ.idx.filter fun r => (λ.ped r).at_layer (l-1) = e_prev) =
        (λ.idx.filter fun r => (λ.ped r).restrict (l-1) = P.pedigree) := by
      ext r
      simp
      constructor
      · intro h
        exact rigid_determines_extension P hP (λ.ped r) h.1 h.2
      · intro h
        simp [h, P.edge_at_layer_eq]

    rw [← h_outflow, h_supply, h_supply_eq_μ, ← h_eq_filters]
    rw [hk_eq_l]

  case step k hk_ge_l hk_le_prev IH =>
    -- Inductive step: assume true for k, prove for k+1

    -- Project λ to layer k
    let λ_bar : ConvexWitness n k X := {
      idx := λ.idx.image (fun r => (λ.ped r).restrict k)
      weight := fun s => ∑ r ∈ λ.idx.filter (fun r => (λ.ped r).restrict k = s), λ.weight r
      h_nonneg := by
        intro s hs
        apply Finset.sum_nonneg
        intro r hr
        exact le_of_lt (λ.wt_pos r hr.1)
      h_sum := by
        calc
          ∑ s ∈ _, ∑ r ∈ λ.idx.filter (fun r => (λ.ped r).restrict k = s), λ.weight r
            = ∑ r ∈ λ.idx, λ.weight r := by
              rw [← Finset.sum_biUnion]
              · intro s1 hs1 s2 hs2 hne
                simp [Finset.disjoint_iff]
                intro r hr1 hr2
                have h_eq : s1 = s2 := by
                  rw [← hr1.2, ← hr2.2]
                contradiction
              · simp [Finset.biUnion_image]
          _ = 1 := λ.wt_sum
      h_pos := by
        intro s hs
        simp at hs
        obtain ⟨r, hr, h_eq⟩ := hs
        have : λ.weight r ≤ ∑ r' ∈ λ.idx.filter (fun r' => (λ.ped r').restrict k = s), λ.weight r' :=
          Finset.single_le_sum (fun r' hr' => le_of_lt (λ.wt_pos r' hr'.1)) (by simp [hr, h_eq])
        linarith [λ.wt_pos r hr]
      h_rep := by
        intro t
        calc
          X t = ∑ r ∈ λ.idx, λ.weight r * ((λ.ped r) t) := λ.combo t
          _ = ∑ s ∈ _, ∑ r ∈ λ.idx.filter (fun r => (λ.ped r).restrict k = s),
                λ.weight r * ((λ.ped r) t) := by
              rw [← Finset.sum_biUnion]
              · intro s1 hs1 s2 hs2 hne
                simp [Finset.disjoint_iff]
                intro r hr1 hr2
                have h_eq : s1 = s2 := by
                  rw [← hr1.2, ← hr2.2]
                contradiction
              · simp [Finset.biUnion_image]
          _ = ∑ s ∈ _, (∑ r ∈ λ.idx.filter (fun r => (λ.ped r).restrict k = s), λ.weight r) * (s t) := by
              apply Finset.sum_congr rfl
              intro s hs
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r hr
              congr 1
              exact (hr.2).symm
    }

    -- Apply induction hypothesis to λ_bar
    have IH_applied : ∑ s ∈ λ_bar.idx.filter (fun s => s ∈ EXT P k), λ_bar.weight s =
        net.μ_weight P :=
      IH λ_bar (by -- λ_bar represents X/k by construction
        exact λ_bar.h_rep
      )

    -- Expand the sum
    have h_expand : ∑ s ∈ λ_bar.idx.filter (fun s => s ∈ EXT P k), λ_bar.weight s =
        ∑ s ∈ EXT P k, ∑ r ∈ λ.idx.filter (fun r => (λ.ped r).restrict k = s), λ.weight r := by
      simp [λ_bar]
      rw [← Finset.sum_biUnion]
      · apply Finset.sum_congr rfl
        intro s hs
        simp [Finset.filter_filter]
      · intro s1 hs1 s2 hs2 hne
        simp [Finset.disjoint_iff]
        intro r hr1 hr2
        have h_eq : s1 = s2 := by
          rw [← hr1.2, ← hr2.2]
        contradiction

    -- Relate to extensions to k+1
    have h_relate : ∑ s ∈ EXT P k, ∑ r ∈ λ.idx.filter (fun r => (λ.ped r).restrict k = s), λ.weight r =
        ∑ r ∈ λ.idx.filter (fun r => (λ.ped r) ∈ EXT P (k + 1)), λ.weight r := by
      apply Finset.sum_biUnion
      · intro s1 hs1 s2 hs2 hne
        simp [Finset.disjoint_iff]
        intro r hr1 hr2
        have h_eq : s1 = s2 := by
          rw [← hr1.2, ← hr2.2]
        contradiction
      · ext r
        simp [EXT]
        constructor
        · intro ⟨s, hs, hr⟩
          have h_restrict : (λ.ped r).restrict k = s := hr.2
          rw [← h_restrict] at hs
          exact hs
        · intro h
          use (λ.ped r).restrict k
          constructor
          · simp [EXT, h]
          · simp

    rw [← h_relate, ← h_expand, IH_applied]

end MembershipProject.Core
