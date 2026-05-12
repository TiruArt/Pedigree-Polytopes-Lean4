-- Core/N_ExistsSwapPedigree_T.lean
-- Existence of a swapped pedigree R for a closed set C of discords.

import Mathlib.Tactic
import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_PedigreeDefinition
import MembershipProject.Core.N_Discords
import MembershipProject.Core.N_Checking_Welded2_T

namespace MembershipProject.Core

lemma exists_swap_pedigree {n : ℕ} (P Q : Pedigree n) (C : Finset ℕ)
    (h_sub : C ⊆ discords P Q)
    (h_proper : C ≠ ∅ ∧ C ≠ discords P Q)
    (h_closed : ∀ (q_l q_m : ℕ), q_l ∈ discords P Q → q_m ∈ discords P Q → q_l ∈ C → welded P Q (min q_l q_m) (max q_l q_m) → q_m ∈ C) :
    ∃ R : Pedigree n, R ≠ P ∧ R ≠ Q ∧
      (∀ t : Triple, t.k ≤ n → char_vec R t = 1 → char_vec P t = 1 ∨ char_vec Q t = 1) ∧
      (∀ t : Triple, t.k ≤ n → char_vec P t = 1 ∧ char_vec Q t = 1 → char_vec R t = 1) :=
  by
    -- Construct R_triangles
    let R_triangles : List Triple := List.ofFn (fun (i : Fin (n - 2)) =>
      let k := i.val + 3
      if k ∈ C then
        (Q.triangles.get ⟨i.val, by rw [Q.h_length]; exact i.isLt⟩)
      else
        (P.triangles.get ⟨i.val, by rw [P.h_length]; exact i.isLt⟩)
    )

    -- Length
    have hR_len : R_triangles.length = n - 2 := by
      simp [R_triangles, List.length_ofFn]

    -- First element
    have hR_first : R_triangles.head? = some (1, 2, 3) := by
      simp [R_triangles, List.ofFn, List.head?_ofFn, Fin.val_zero]
      have h3_notin_C : 3 ∉ C := by
        intro h
        have h3_disc : 3 ∈ discords P Q := h_sub h
        simp [discords, Finset.mem_Ico] at h3_disc
        omega
      rw [if_neg h3_notin_C]
      exact P.h_first

    -- Layers
    have hR_layers : ∀ i (hi : i < R_triangles.length), (R_triangles.get ⟨i, hi⟩).k = i + 3 := by
      intro i hi
      simp [R_triangles, List.get_ofFn]
      let k := i + 3
      by_cases hkC : k ∈ C
      · have hQ := Q.h_layers i (by rw [Q.h_length]; omega)
        simp [hkC]
        exact hQ
      · have hP := P.h_layers i (by rw [P.h_length]; omega)
        simp [hkC]
        exact hP

    -- In delta
    have hR_in_delta : ∀ i (hi : i < R_triangles.length), R_triangles.get ⟨i, hi⟩ ∈ Delta (R_triangles.get ⟨i, hi⟩).k := by
      intro i hi
      simp [R_triangles, List.get_ofFn]
      let k := i + 3
      by_cases hkC : k ∈ C
      · have hQ := Q.h_in_delta i (by rw [Q.h_length]; omega)
        simp [hkC]
        exact hQ
      · have hP := P.h_in_delta i (by rw [P.h_length]; omega)
        simp [hkC]
        exact hP

    -- Generators
    have hR_generators : ∀ i (hi : i < R_triangles.length), i > 0 →
        ∃ j (hj : j < i), (R_triangles.get ⟨j, hj⟩) ∈ generators (R_triangles.get ⟨i, hi⟩) := by
      intro i hi i_pos
      let k := i + 3
      by_cases hkC : k ∈ C
      · -- k ∈ C: use Q
        have hiQ : i < Q.triangles.length := by rw [Q.h_length]; omega
        have hgenQ := Q.h_generators i i_pos hiQ
        obtain ⟨j, hjQ, hgen⟩ := hgenQ
        have hj : j < i := hjQ
        have hjC : (j + 3) ∈ C := by
          by_contra hnotC
          have h_weld : welded P Q (min (j+3) k) (max (j+3) k) := by
            have h_lt : j+3 < k := by omega
            have h_edge_Q_m := Q.h_layers i hiQ
            have h_edge_Q_l := Q.h_layers j (by omega)
            apply Or.inl (Or.inl ⟨by omega, h_lt, _⟩)
            simp [h_edge_Q_l, h_edge_Q_m, hgen]
          exact h_closed (j+3) k (by omega) (by omega) (by omega) h_weld hnotC
        have hjR : j < R_triangles.length := by rw [hR_len]; omega
        have hgetRj : R_triangles.get ⟨j, hjR⟩ = Q.triangles.get ⟨j, hjQ⟩ := by
          simp [R_triangles, hjC]
        rw [hgetRj]
        have hgetRi : R_triangles.get ⟨i, hi⟩ = Q.triangles.get ⟨i, hiQ⟩ := by
          simp [R_triangles, hkC]
        rw [hgetRi]
        exact ⟨j, hj, hgen⟩
      · -- k ∉ C: use P
        have hiP : i < P.triangles.length := by rw [P.h_length]; omega
        have hgenP := P.h_generators i i_pos hiP
        obtain ⟨j, hjP, hgen⟩ := hgenP
        have hj : j < i := hjP
        have hjC : (j + 3) ∉ C := by
          by_contra hC
          have h_weld : welded P Q (min (j+3) k) (max (j+3) k) := by
            have h_lt : j+3 < k := by omega
            have h_edge_P_m := P.h_layers i hiP
            have h_edge_P_l := P.h_layers j (by omega)
            apply Or.inl (Or.inl ⟨by omega, h_lt, _⟩)
            simp [h_edge_P_l, h_edge_P_m, hgen]
          exact hkC (h_closed (j+3) k (by omega) (by omega) (by omega) h_weld hC)
        have hjR : j < R_triangles.length := by rw [hR_len]; omega
        have hgetRj : R_triangles.get ⟨j, hjR⟩ = P.triangles.get ⟨j, hjP⟩ := by
          simp [R_triangles, hjC]
        rw [hgetRj]
        have hgetRi : R_triangles.get ⟨i, hi⟩ = P.triangles.get ⟨i, hiP⟩ := by
          simp [R_triangles, hkC]
        rw [hgetRi]
        exact ⟨j, hj, hgen⟩

    -- Distinctness
    have hR_distinct : ∀ i j (hi : i < R_triangles.length) (hj : j < R_triangles.length),
        i > 0 → j > 0 → i ≠ j →
        ((R_triangles.get ⟨i, hi⟩).i, (R_triangles.get ⟨i, hi⟩).j) ≠
        ((R_triangles.get ⟨j, hj⟩).i, (R_triangles.get ⟨j, hj⟩).j) := by
      intro i j hi hj i_pos j_pos hij
      let k_i := i + 3
      let k_j := j + 3

      have hiP : i < P.triangles.length := by rw [P.h_length]; omega
      have hjP : j < P.triangles.length := by rw [P.h_length]; omega
      have hiQ : i < Q.triangles.length := by rw [Q.h_length]; omega
      have hjQ : j < Q.triangles.length := by rw [Q.h_length]; omega

      by_cases h_i_in_C : k_i ∈ C
      · by_cases h_j_in_C : k_j ∈ C
        · -- Both in C: use Q
          have hRi : R_triangles.get ⟨i, hi⟩ = Q.triangles.get ⟨i, hiQ⟩ := by simp [R_triangles, h_i_in_C]
          have hRj : R_triangles.get ⟨j, hj⟩ = Q.triangles.get ⟨j, hjQ⟩ := by simp [R_triangles, h_j_in_C]
          rw [hRi, hRj]
          exact Q.h_distinct i j hiQ hjQ i_pos j_pos hij
        · -- i in C, j not in C
          have hRi : R_triangles.get ⟨i, hi⟩ = Q.triangles.get ⟨i, hiQ⟩ := by simp [R_triangles, h_i_in_C]
          have hRj : R_triangles.get ⟨j, hj⟩ = P.triangles.get ⟨j, hjP⟩ := by simp [R_triangles, h_j_in_C]
          rw [hRi, hRj]
          by_contra h_eq
          have h_eq_edge : edge_at Q k_i = edge_at P k_j := by
            simp [edge_at, hiQ, hjP] at h_eq
            exact h_eq
          by_cases h_kj_disc : k_j ∈ discords P Q
          · -- k_j is a discord: welding forces k_j ∈ C
            have h_weld : welded P Q (min k_i k_j) (max k_i k_j) := by
              have h_lt : k_i < k_j := by omega
              apply Or.inr (Or.inl (Or.inr ?_))
              use k_j
              constructor
              · exact h_lt
              · simp [edge_at, hiQ] at h_eq_edge
                exact h_eq_edge
            have h_kj_in_C := h_closed k_i k_j (by omega) (by omega) (by omega) h_weld h_i_in_C
            exact h_j_in_C h_kj_in_C
          · -- k_j not a discord: then edge_at P k_j = edge_at Q k_j
            have h_eq_PQ : edge_at P k_j = edge_at Q k_j := by
              simp [discords, Finset.mem_Ico, h_j_in_C] at h_kj_disc
              exact h_kj_disc
            rw [h_eq_edge, h_eq_PQ] at h_eq_edge
            have h_distinct_Q := Q.h_distinct i j hiQ hjQ i_pos j_pos hij
            simp [edge_at, hiQ, hjQ] at h_distinct_Q
            exact h_distinct_Q h_eq_edge
      · by_cases h_j_in_C : k_j ∈ C
        · -- i not in C, j in C (symmetric)
          have hRi : R_triangles.get ⟨i, hi⟩ = P.triangles.get ⟨i, hiP⟩ := by simp [R_triangles, h_i_in_C]
          have hRj : R_triangles.get ⟨j, hj⟩ = Q.triangles.get ⟨j, hjQ⟩ := by simp [R_triangles, h_j_in_C]
          rw [hRi, hRj]
          by_contra h_eq
          have h_eq_edge : edge_at P k_i = edge_at Q k_j := by
            simp [edge_at, hiP, hjQ] at h_eq
            exact h_eq
          by_cases h_ki_disc : k_i ∈ discords P Q
          · have h_weld : welded P Q (min k_i k_j) (max k_i k_j) := by
              have h_lt : k_i < k_j := by omega
              apply Or.inr (Or.inl (Or.inr ?_))
              use k_i
              constructor
              · exact h_lt
              · simp [edge_at, hjQ] at h_eq_edge
                exact h_eq_edge.symm
            have h_ki_in_C := h_closed k_j k_i (by omega) (by omega) (by omega) h_weld h_j_in_C
            exact h_i_in_C h_ki_in_C
          · have h_eq_PQ : edge_at P k_i = edge_at Q k_i := by
              simp [discords, Finset.mem_Ico, h_i_in_C] at h_ki_disc
              exact h_ki_disc
            rw [h_eq_edge, h_eq_PQ] at h_eq_edge
            have h_distinct_Q := Q.h_distinct i j hiQ hjQ i_pos j_pos hij
            simp [edge_at, hiQ, hjQ] at h_distinct_Q
            exact h_distinct_Q h_eq_edge
        · -- Neither in C: use P
          have hRi : R_triangles.get ⟨i, hi⟩ = P.triangles.get ⟨i, hiP⟩ := by simp [R_triangles, h_i_in_C]
          have hRj : R_triangles.get ⟨j, hj⟩ = P.triangles.get ⟨j, hjP⟩ := by simp [R_triangles, h_j_in_C]
          rw [hRi, hRj]
          exact P.h_distinct i j hiP hjP i_pos j_pos hij

    -- Construct R
    let R : Pedigree n := ⟨R_triangles, P.h_n, hR_len, hR_first, hR_layers, hR_generators, hR_distinct, hR_in_delta⟩

    -- R ≠ P
    have hR_ne_P : R ≠ P := by
      obtain ⟨q, hq⟩ := h_proper.1
      have hq_mem : q ∈ C := hq
      have hq_disc : q ∈ discords P Q := h_sub hq_mem
      have hPq : edge_at P q = (P.triangles.get ⟨q-3, by rw [P.h_length]; omega⟩).toProd := rfl
      have hRq : edge_at R q = (R_triangles.get ⟨q-3, by rw [hR_len]; omega⟩).toProd := by
        simp [R_triangles, hq_mem]
      exact fun heq => (mem_discords_iff P Q q).mp hq_disc
        (same_edge_same_triple P Q q (by omega) (by omega) (by rw [P.h_length]; omega) (by rw [Q.h_length]; omega) (by rw [heq, hRq, hPq]))

    -- R ≠ Q
    have hR_ne_Q : R ≠ Q := by
      obtain ⟨q, hq⟩ := h_proper.1
      have hq_mem : q ∈ C := hq
      have hq_disc : q ∈ discords P Q := h_sub hq_mem
      have hQq : edge_at Q q = (Q.triangles.get ⟨q-3, by rw [Q.h_length]; omega⟩).toProd := rfl
      have hRq : edge_at R q = (R_triangles.get ⟨q-3, by rw [hR_len]; omega⟩).toProd := by
        simp [R_triangles, hq_mem]
      exact fun heq => (mem_discords_iff P Q q).mp hq_disc
        (same_edge_same_triple P Q q (by omega) (by omega) (by rw [P.h_length]; omega) (by rw [Q.h_length]; omega) (by rw [heq, hRq, hQq]))

    -- Subset condition
    have h_subset_R : ∀ t : Triple, t.k ≤ n → char_vec R t = 1 → char_vec P t = 1 ∨ char_vec Q t = 1 := by
      intro t htk
      simp [char_vec, R_triangles]
      by_cases hC : t.k ∈ C
      · simp [hC]
        intro h
        right
        exact h
      · simp [hC]
        intro h
        left
        exact h

    -- Superset condition
    have h_superset_R : ∀ t : Triple, t.k ≤ n → char_vec P t = 1 ∧ char_vec Q t = 1 → char_vec R t = 1 := by
      intro t htk ⟨hP, hQ⟩
      simp [char_vec, R_triangles]
      by_cases hC : t.k ∈ C
      · exfalso
        have h_disc : t.k ∈ discords P Q := by
          simp [discords, Finset.mem_Ico, htk]
          exact ⟨hC, ne_of_apply_ne (char_vec P t) hP hQ⟩
        exact hC (h_sub h_disc)
      · simp [hC]
        exact hP

    -- Return
    exact ⟨R, hR_ne_P, hR_ne_Q, h_subset_R, h_superset_R⟩

end MembershipProject.Core
