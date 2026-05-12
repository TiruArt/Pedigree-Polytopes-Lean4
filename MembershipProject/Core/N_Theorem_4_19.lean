-- Core/N_Theorem_4_19.lean
-- Theorem 4.19: Swapping a component yields valid pedigrees

import MembershipProject.Core.N_Lemma_4_17
import MembershipProject.Core.N_Welding
import MembershipProject.Core.N_Pedigree

namespace MembershipProject.Core

open Nat Finset

theorem component_swap_valid {n : ℕ} (P Q : Pedigree n) (C : Finset ℕ)
    (hC_comp : ∀ s, s ∈ C → ∀ t, t ∈ discords P Q \ C →
        ¬ (if s < t then welded_to P Q t s else welded_to P Q s t))
    (hC_subset : C ⊆ discords P Q) :
    IsPedigree (swap P Q C) ∧ IsPedigree (swap Q P C) := by
  induction' C using Finset.strongInduction with C ih

  by_cases h_card : card C = 1
  · -- Base case: singleton component
    obtain ⟨l, h_eq⟩ := card_eq_one.mp h_card
    rw [h_eq] at hC_subset
    have hl_in : l ∈ discords P Q := hC_subset (Finset.mem_singleton_self l)
    -- The condition for singleton_swap_valid follows from hC_comp
    have h_comp_singleton : ∀ s, s ≠ l → ¬ (if s < l then welded_to P Q l s else welded_to P Q s l) := by
      intro s hs_neq
      by_cases hs_disc : s ∈ discords P Q
      · by_cases hs_lt : s < l
        · have h_not_in_C : s ∉ C := by simp [h_eq, hs_neq]
          exact hC_comp l (by simp) s (by simp [hs_neq, hs_lt, hs_disc, h_not_in_C]) (by simp [hs_lt])
        · have hs_gt : s > l := by omega
          have h_not_in_C : s ∉ C := by simp [h_eq, hs_neq]
          exact hC_comp s (by simp [hs_neq, hs_gt, hs_disc]) l (by simp) (by simp [hs_gt])
      · -- s is not a discord, so welded_to is false
        simp [welded_to]
        exact fun h => h.2.1 hs_disc
    exact singleton_swap_valid h_comp_singleton hl_in

  · -- Inductive case: |C| > 1
    -- The proof follows Chapter 4, Theorem 4.19
    sorry

end MembershipProject.Core
