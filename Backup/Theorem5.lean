-- Core/Theorem5.lean
-- ========================================================
-- Theorem 5: Necessity
-- Paper: "A Strongly Polynomial Algorithm for Membership
--        in the Pedigree Polytope" by Tiru Arthanari
-- Section 6.2, page 26
-- ========================================================

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import MembershipProject.Core.LayeredNetwork
import MembershipProject.Core.MCF
import MembershipProject.Core.Lemma6

namespace MembershipProject.Core

open Finset BigOperators

variable {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
variable (X : LayeredPoint n) (net : LayeredNetwork n k)
variable (h_well_defined : net.well_defined)
variable (hX : X/(k+1) ∈ conv(P_{k+1}))

/-- Theorem 5: Necessity -/
theorem theorem_5_necessity :
    ∃ (mcf : MCF k net), mcf.total_flow = z_max net := by

  obtain ⟨λ, hλ⟩ := hX

  def agrees (r : ℕ) (a : Arc) : Prop :=
    match a with
    | Arc.node_to_node u v =>
        (λ.ped r).at_layer u.k = u ∧ (λ.ped r).at_layer (u.k+1) = v
    | Arc.rigid_to_node P v =>
        (λ.ped r).restrict (k-1) = P ∧ (λ.ped r).at_layer (k+1) = v

  let f (a : Arc) : ℚ :=
    ∑ r ∈ λ.idx.filter (fun r => agrees r a), λ.weight r

  let f_s (s : Commodity k) (a : Arc) : ℚ :=
    let a_s := designating_arc s
    ∑ r ∈ λ.idx.filter (fun r => agrees r a_s ∧ agrees r a), λ.weight r

  have h_nonneg : ∀ s a, 0 ≤ f_s s a := by
    intro s a
    unfold f_s
    apply Finset.sum_nonneg
    intro r hr
    exact le_of_lt (λ.wt_pos r hr.1)

  have h_conservation : ∀ s v, v ∉ net.sources ∪ net.sinks →
      ∑ a ∈ incoming v, f_s s a = ∑ a ∈ outgoing v, f_s s a := by
    intro s v hv
    unfold f_s
    rw [← Finset.sum_comm, ← Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    have h_ped_cons : (λ.ped r).flow_conservation v :=
      pedigree_flow_conservation (λ.ped r) v hv
    simp [h_ped_cons, mul_sum]

  have h_decomposition : ∀ a, f a = ∑ s ∈ commodities, f_s s a := by
    intro a
    unfold f f_s
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    have h_unique : ∃! s, agrees r (designating_arc s) :=
      unique_designating_arc_for_pedigree (λ.ped r)
    obtain ⟨s, hs, h_unique⟩ := h_unique
    simp [hs, h_unique]

  have h_node_cap : ∀ v, ∑ s ∑ a ∈ incoming v, f_s s a ≤ net.node_cap v := by
    intro v
    unfold f_s
    calc
      ∑ s ∑ a ∈ incoming v, ∑ r ∈ λ.idx.filter (fun r => agrees r (designating_arc s) ∧ agrees r a), λ.weight r
        = ∑ r ∈ λ.idx, λ.weight r *
            (if (λ.ped r).uses_node v then 1 else 0) := by
          sorry
      _ = net.node_cap v := by
          sorry

  have h_total_flow : ∑ a ∈ F_k.arcs, f a = z_max net := by
    unfold f z_max
    calc
      ∑ a ∈ F_k.arcs, ∑ r ∈ λ.idx.filter (fun r => agrees r a), λ.weight r
        = ∑ r ∈ λ.idx, λ.weight r *
            (1 - if (λ.ped r) ∈ net.R_k then 1 else 0) := by
          sorry
      _ = 1 - ∑ P ∈ net.R_k, ∑ r ∈ λ.idx.filter (fun r => (λ.ped r) = P), λ.weight r := by
          rw [Finset.sum_sub_distrib]
          sorry
      _ = 1 - ∑ P ∈ net.R_k, net.μ P := by
          apply Finset.sum_congr rfl
          intro P hP
          exact extension_lemma λ P hP
      _ = z_max net := rfl

  let mcf : MCF k net := {
    commodities := all_commodities net
    f := f
    f_s := f_s
    f_s_nonneg := h_nonneg
    conservation := h_conservation
    decomposition := h_decomposition
    node_capacity := h_node_cap
    total_flow_eq := h_total_flow
  }

  exact ⟨mcf, h_total_flow⟩

end MembershipProject.Core
