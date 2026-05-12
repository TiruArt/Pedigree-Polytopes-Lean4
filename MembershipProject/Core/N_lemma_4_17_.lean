-- Core/N_Lemma_4_17.lean
-- Lemma 4.17: Singleton component swap yields valid pedigree

import MembershipProject.Core.N_Swap
import MembershipProject.Core.N_Welding
import MembershipProject.Core.N_Pedigree

namespace MembershipProject.Core

open Nat Finset

def IsPedigree {n : ℕ} (P : Pedigree n) : Prop :=
  (∀ k, 3 ≤ k → k ≤ n → P.triple_at k ∈ Delta k) ∧
  P.triple_at 3 = (1, 2, 3) ∧
  (∀ k1 k2, 4 ≤ k1 → k1 < k2 → k2 ≤ n → P.triple_at k1 ≠ P.triple_at k2) ∧
  (∀ k, 4 ≤ k → k ≤ n →
    let t := P.triple_at k
    let (_, b, _) := t
    if b > 3 then P.triple_at b ∈ generators t
    else P.triple_at 3 ∈ generators t)

lemma singleton_swap_valid {n : ℕ} {P Q : Pedigree n} {l : ℕ}
    (h_comp : ∀ s, s ≠ l → ¬ (if s < l then welded_to P Q l s else welded_to P Q s l))
    (hl_in : l ∈ discords P Q) :
    IsPedigree (swap P Q {l}) := by
  let Y := swap P Q {l}

  have h_l_ge_4 : 4 ≤ l := by
    simp [mem_discords_iff] at hl_in
    exact hl_in.1
  have h_l_le_n : l ≤ n := by
    simp [mem_discords_iff] at hl_in
    exact hl_in.2.1
  have h_3_lt_l : 3 < l := by omega

  -- Helper: no welds from l to any s < l
  have h_no_weld : ∀ s, s < l → ¬ welded_to P Q l s := by
    intro s hs_lt
    intro h_weld
    have h_contra := h_comp s (by linarith) (by simp [hs_lt, h_weld])
    exact h_contra

  constructor
  · -- Range condition
    intro k hk_ge hk_le
    by_cases hk_eq_l : k = l
    · subst hk_eq_l
      simp [swap]
      exact Q.h_k_range l (by omega) (by omega)
    · simp [swap, hk_eq_l]
      exact P.h_k_range k hk_ge hk_le

  · constructor
    · -- Base triple
      have h_3_ne_l : 3 ≠ l := by omega
      simp [swap, h_3_ne_l]
      exact P.h_base

    · constructor
      · -- Distinctness
        intro k1 k2 hk1_ge hk12 hk2_le
        by_cases hk1_eq_l : k1 = l
        · by_cases hk2_eq_l : k2 = l
          · contradiction
          · -- k1 = l, k2 ≠ l
            have h_eq : Q.triple_at l = P.triple_at k2 := by
              simp [swap, hk1_eq_l, hk2_eq_l]
            have h_k2_discord : k2 ∈ discords P Q := by
              by_contra h_not
              have h_agree : P.triple_at k2 = Q.triple_at k2 :=
                not_discord_agree P Q (by omega) (by omega) h_not
              rw [h_agree] at h_eq
              have h_diff : P.triple_at k2 ≠ Q.triple_at k2 :=
                (mem_discords_iff P Q).mp hl_in |>.2.2
              contradiction
            have h_weld : welded_to P Q k2 l :=
              ⟨l, by omega, hl_in, h_k2_discord, ⟨true, Or.inr ⟨l, by omega, hl_in, h_eq⟩⟩⟩
            have h_contra := h_comp k2 (by linarith) (by simp [hk12, h_weld])
            exact h_contra
        · by_cases hk2_eq_l : k2 = l
          · -- k1 ≠ l, k2 = l
            have h_eq : P.triple_at k1 = Q.triple_at l := by
              simp [swap, hk1_eq_l, hk2_eq_l]
            have h_k1_discord : k1 ∈ discords P Q := by
              by_contra h_not
              have h_agree : P.triple_at k1 = Q.triple_at k1 :=
                not_discord_agree P Q (by omega) (by omega) h_not
              rw [h_agree] at h_eq
              have h_diff : P.triple_at k1 ≠ Q.triple_at k1 :=
                (mem_discords_iff P Q).mp hl_in |>.2.2
              contradiction
            have h_weld : welded_to P Q l k1 :=
              ⟨k1, by omega, h_k1_discord, hl_in, ⟨false, Or.inr ⟨k1, by omega, h_k1_discord, h_eq⟩⟩⟩
            have h_contra := h_comp k1 (by linarith) (by simp [hk12, h_weld])
            exact h_contra
          · -- k1 ≠ l, k2 ≠ l
            have h_eq : P.triple_at k1 = P.triple_at k2 := by
              simp [swap, hk1_eq_l, hk2_eq_l]
            exact P.h_distinct k1 k2 hk1_ge hk12 hk2_le h_eq

      · -- Generator property
        intro k hk_ge hk_le
        by_cases hk_eq_l : k = l
        · -- Case k = l
          let t := Q.triple_at l
          let (a, b, _) := t
          have h_b_lt_l : b < l := by
            obtain ⟨_, _, hb⟩ := mem_Delta_iff.mp (Q.h_k_range l (by omega) (by omega))
            exact hb.2.1
          if h_b_le_3 : b ≤ 3 then
            -- generator is (1,2,3)
            have h_gen : (1,2,3) ∈ generators t := by
              have h_not_base : ¬ (a = 1 ∧ b = 2) := by
                intro h
                have h_in_D : (1,2,l) ∈ discords P Q := by
                  simp [mem_discords_iff]
                  exact ⟨h_l_ge_4, h_l_le_n, by simp [h]⟩
                exact h_in_D hl_in
              simp [generators, h_b_le_3, h_not_base]
            have h_3_lt_l : 3 < l := by omega
            have h_available : Y.triple_at 3 = (1,2,3) := by
              simp [swap, h_3_lt_l]
              exact P.h_base
            rw [h_available]
            exact h_gen
          else
            have h_b_gt_3 : b > 3 := by omega
            have h_gen : P.triple_at b ∈ generators t :=
              Q.h_generator l (by omega) (by omega) h_b_gt_3
            have h_b_lt_l : b < l := h_b_lt_l
            have h_available : Y.triple_at b = P.triple_at b := by
              simp [swap, h_b_lt_l]
            rw [h_available]
            exact h_gen
        · -- Case k ≠ l
          let t := P.triple_at k
          let (a, b, _) := t
          have h_b_lt_k : b < k := by
            obtain ⟨_, _, hb⟩ := mem_Delta_iff.mp (P.h_k_range k (by omega) (by omega))
            exact hb.2.1
          if h_b_le_3 : b ≤ 3 then
            have h_gen : (1,2,3) ∈ generators t := by
              have h_not_base : ¬ (a = 1 ∧ b = 2) := by
                intro h
                have h_in_D : (1,2,l) ∈ discords P Q := by
                  simp [mem_discords_iff]
                  exact ⟨h_l_ge_4, h_l_le_n, by simp [h]⟩
                exact h_in_D hl_in
              simp [generators, h_b_le_3, h_not_base]
            have h_3_lt_k : 3 < k := by omega
            have h_available : Y.triple_at 3 = (1,2,3) := by
              simp [swap, h_3_lt_k]
              exact P.h_base
            rw [h_available]
            exact h_gen
          else
            have h_b_gt_3 : b > 3 := by omega
            if h_b_eq_l : b = l then
              have h_gen : Q.triple_at l ∈ generators t :=
                Q.h_generator l (by omega) (by omega) h_b_gt_3
              have h_l_lt_k : l < k := by
                rw [← h_b_eq_l] at h_b_lt_k
                exact h_b_lt_k
              have h_available : Y.triple_at l = Q.triple_at l := by
                simp [swap, h_l_lt_k]
              rw [h_available]
              exact h_gen
            else
              have h_gen : P.triple_at b ∈ generators t :=
                P.h_generator k (by omega) (by omega) h_b_gt_3
              have h_b_lt_k : b < k := h_b_lt_k
              have h_available : Y.triple_at b = P.triple_at b := by
                simp [swap, h_b_eq_l, h_b_lt_k]
              rw [h_available]
              exact h_gen

end MembershipProject.Core
