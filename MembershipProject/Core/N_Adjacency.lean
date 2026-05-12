-- Core/N_Adjacency.lean
-- Adjacency in Pedigree Polytope: Graph of Rigidity characterization

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_RestrictionFull
import MembershipProject.Core.N_Types
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MembershipProject.Core

open Nat Finset SimpleGraph

-- ============================================================
-- PEDIGREE structure
-- ============================================================

structure Pedigree (n : ℕ) where
  triple_at : ℕ → Triple
  h3       : 3 ≤ n
  h_k_range : ∀ k, 3 ≤ k → k ≤ n → triple_at k ∈ Delta k
  h_base   : triple_at 3 = (1, 2, 3)
  h_distinct : ∀ k1 k2, 4 ≤ k1 → k1 < k2 → k2 ≤ n → triple_at k1 ≠ triple_at k2

-- ============================================================
-- Convert pedigree to 0-1 LayeredPoint
-- ============================================================

def to_layered {n : ℕ} (P : Pedigree n) : LayeredPoint n :=
  fun t => if P.triple_at t.k = t then 1 else 0

-- ============================================================
-- Midpoint of two pedigrees
-- ============================================================

def midpoint {n : ℕ} (P Q : Pedigree n) : LayeredPoint n :=
  fun t => (to_layered P t + to_layered Q t) / 2

-- ============================================================
-- Discords
-- ============================================================

def discords {n : ℕ} (P Q : Pedigree n) : Finset ℕ :=
  Finset.filter (fun k => P.triple_at k ≠ Q.triple_at k) (Ico 4 (n + 1))

lemma mem_discords_iff {n : ℕ} (P Q : Pedigree n) {k : ℕ} :
    k ∈ discords P Q ↔ 4 ≤ k ∧ k ≤ n ∧ P.triple_at k ≠ Q.triple_at k := by
  simp [discords, mem_filter, mem_Ico]
  tauto

lemma not_discord_agree {n : ℕ} (P Q : Pedigree n) {k : ℕ}
    (hk : 4 ≤ k) (hk' : k ≤ n) (h : k ∉ discords P Q) :
    P.triple_at k = Q.triple_at k := by
  simp [mem_discords_iff, hk, hk'] at h
  tauto

-- ============================================================
-- Pedigree is 0-1 valued
-- ============================================================

lemma pedigree_is_01 {n : ℕ} (P : Pedigree n) (t : Triple) :
    to_layered P t = 0 ∨ to_layered P t = 1 := by
  simp [to_layered]
  by_cases h : P.triple_at t.k = t
  · right; exact h
  · left; exact h

-- ============================================================
-- Single discord properties
-- ============================================================

lemma single_discord_properties {n : ℕ} {P Q : Pedigree n}
    (h : card (discords P Q) = 1) :
    ∃ q, 4 ≤ q ∧ q ≤ n ∧
      (∀ k, 3 ≤ k → k ≤ n → k ≠ q → P.triple_at k = Q.triple_at k) := by
  obtain ⟨q, hq⟩ := card_eq_one.mp h
  have hq_mem : q ∈ discords P Q := by rw [hq]; simp
  have hq_range : 4 ≤ q ∧ q ≤ n := by
    have hq_mem' := (mem_discords_iff P Q).mp hq_mem
    exact ⟨hq_mem'.1, hq_mem'.2.1⟩

  have h_agree : ∀ k, 3 ≤ k → k ≤ n → k ≠ q → P.triple_at k = Q.triple_at k := by
    intro k hk_ge hk_le hk_neq
    by_contra h_neq
    by_cases hk_eq3 : k = 3
    · subst hk_eq3
      rw [P.h_base, Q.h_base] at h_neq
      contradiction
    · have hk_ge4 : 4 ≤ k := by omega
      have hk_discord : k ∈ discords P Q := by
        simp [mem_discords_iff, hk_ge4, hk_le, h_neq]
      rw [hq] at hk_discord
      simp at hk_discord
      exact hk_neq hk_discord

  exact ⟨q, hq_range.1, hq_range.2, h_agree⟩

-- ============================================================
-- Definition of adjacency
-- ============================================================

def AdjacentInPolytope {n : ℕ} (P Q : Pedigree n) : Prop :=
  ∀ (S : Finset (Pedigree n)) (μ : Pedigree n → ℚ),
    (∑ Y in S, μ Y = 1) →
    (∀ Y ∈ S, 0 < μ Y) →
    (∀ t, midpoint P Q t = ∑ Y in S, μ Y * to_layered Y t) →
    S = {P, Q}

def NonadjacentInPolytope {n : ℕ} (P Q : Pedigree n) : Prop :=
  ¬ AdjacentInPolytope P Q

-- ============================================================
-- LEMMA 4.13: Single discord implies adjacency
-- ============================================================

theorem adjacent_if_single_discord {n : ℕ} (P Q : Pedigree n)
    (h_single : card (discords P Q) = 1) :
    AdjacentInPolytope P Q := by
  obtain ⟨q, hq_ge, hq_le, h_agree⟩ := single_discord_properties h_single
  intro S μ h_sum h_pos h_mid

  have h_agree_others : ∀ k, 3 ≤ k → k ≤ n → k ≠ q → P.triple_at k = Q.triple_at k :=
    h_agree

  have h_match : ∀ Y ∈ S, ∀ k, 3 ≤ k → k ≤ n → k ≠ q → Y.triple_at k = P.triple_at k := by
    intro Y hY k hk_ge hk_le hk_neq
    let t0 := P.triple_at k
    have h_mid_t0 : midpoint P Q t0 = 1 := by
      simp [midpoint, to_layered, h_agree_others k hk_ge hk_le hk_neq]
      norm_num
    have h_sum_t0 := h_mid t0
    rw [h_mid_t0] at h_sum_t0
    have h_Y_t0 : to_layered Y t0 = 1 := by
      by_contra h_zero
      have h_Y_le : to_layered Y t0 ≤ 0 := by
        cases pedigree_is_01 Y t0 with
        | inl h => exact h
        | inr h => linarith [h, h_zero]
      have h_sum_le : ∑ Z in S, μ Z * to_layered Z t0 ≤
          (∑ Z in S \ {Y}, μ Z) * 1 + μ Y * 0 := by
        apply sum_le_sum
        intro Z hZ
        by_cases h_eq : Z = Y
        · subst h_eq; simp [h_Y_le]
        · cases pedigree_is_01 Z t0 with
          | inl h => simp [h]
          | inr h => simp [h]
      simp at h_sum_le
      have h_rest : ∑ Z in S \ {Y}, μ Z = 1 - μ Y := by
        rw [← h_sum]
        apply sum_eq_sum_of_subset
        simp
      rw [h_rest] at h_sum_le
      linarith [h_sum_t0, h_sum_le]
    simp [to_layered] at h_Y_t0
    split_ifs at h_Y_t0 with h_eq
    · exact h_eq
    · simp at h_Y_t0

  have h_either : ∀ Y ∈ S, Y = P ∨ Y = Q := by
    intro Y hY
    let tP := P.triple_at q
    let tQ := Q.triple_at q
    have h_match_q : ∀ k, 3 ≤ k → k ≤ n → k ≠ q → Y.triple_at k = P.triple_at k :=
      h_match Y hY
    by_cases h_Y_tP : Y.triple_at q = tP
    · left
      ext k hk_ge hk_le
      by_cases hk_eq_q : k = q
      · subst hk_eq_q; exact h_Y_tP
      · exact h_match_q k hk_ge hk_le hk_eq_q
    · right
      have h_diff : tP ≠ tQ := by
        rw [← mem_discords_iff] at h_single
        exact h_single.2.2
      have h_Y_tQ : Y.triple_at q = tQ := by
        by_contra h_neither
        have h_Y_tP_zero : to_layered Y tP = 0 := by simp [to_layered, h_Y_tP]
        have h_sum_tP := h_mid tP
        have h_mid_tP : midpoint P Q tP = 1/2 := by
          simp [midpoint, to_layered, h_diff]
          norm_num
        rw [h_mid_tP] at h_sum_tP
        have h_sum_le : ∑ Z in S, μ Z * to_layered Z tP ≤
            (∑ Z in S \ {Y}, μ Z) * 1 + μ Y * 0 := by
          apply sum_le_sum
          intro Z hZ
          by_cases h_eq : Z = Y
          · subst h_eq; simp [h_Y_tP_zero]
          · cases pedigree_is_01 Z tP with
            | inl h => simp [h]
            | inr h => simp [h]
        simp at h_sum_le
        have h_rest : ∑ Z in S \ {Y}, μ Z = 1 - μ Y := by
          rw [← h_sum]
          apply sum_eq_sum_of_subset
          simp
        rw [h_rest] at h_sum_le
        linarith [h_sum_tP, h_sum_le]
      ext k hk_ge hk_le
      by_cases hk_eq_q : k = q
      · subst hk_eq_q; exact h_Y_tQ
      · rw [h_match_q k hk_ge hk_le hk_eq_q]
        exact (h_agree_others k hk_ge hk_le hk_eq_q).symm

  have hS_subset : S ⊆ {P, Q} := by
    intro Y hY
    rcases h_either Y hY with h | h
    · simp [h]
    · simp [h]

  have hP_in : P ∈ S := by
    let tP := P.triple_at q
    have h_mid_tP : midpoint P Q tP = 1/2 := by
      simp [midpoint, to_layered]
      have h_diff : P.triple_at q ≠ Q.triple_at q := by
        rw [← mem_discords_iff] at h_single
        exact h_single.2.2
      simp [h_diff]
      norm_num
    have h_sum_tP := h_mid tP
    rw [h_mid_tP] at h_sum_tP
    by_contra hP_not_in
    have h_sum_le : ∑ Z in S, μ Z * to_layered Z tP ≤ ∑ Z in S \ {P}, μ Z := by
      apply sum_le_sum
      intro Z hZ
      cases pedigree_is_01 Z tP with
      | inl h => simp [h]
      | inr h => simp [h]
    have h_sum_eq : ∑ Z in S \ {P}, μ Z = 1 := by
      rw [← h_sum]
      apply sum_eq_sum_of_subset
      simp [hP_not_in]
    rw [h_sum_eq] at h_sum_le
    linarith [h_sum_tP, h_sum_le]

  have hQ_in : Q ∈ S := by
    let tQ := Q.triple_at q
    have h_mid_tQ : midpoint P Q tQ = 1/2 := by
      simp [midpoint, to_layered]
      have h_diff : P.triple_at q ≠ Q.triple_at q := by
        rw [← mem_discords_iff] at h_single
        exact h_single.2.2
      simp [h_diff.symm]
      norm_num
    have h_sum_tQ := h_mid tQ
    rw [h_mid_tQ] at h_sum_tQ
    by_contra hQ_not_in
    have h_sum_le : ∑ Z in S, μ Z * to_layered Z tQ ≤ ∑ Z in S \ {Q}, μ Z := by
      apply sum_le_sum
      intro Z hZ
      cases pedigree_is_01 Z tQ with
      | inl h => simp [h]
      | inr h => simp [h]
    have h_sum_eq : ∑ Z in S \ {Q}, μ Z = 1 := by
      rw [← h_sum]
      apply sum_eq_sum_of_subset
      simp [hQ_not_in]
    rw [h_sum_eq] at h_sum_le
    linarith [h_sum_tQ, h_sum_le]

  have hS_eq : S = {P, Q} := by
    ext x
    simp
    constructor
    · intro hx
      rcases hS_subset hx with h | h
      · left; exact h
      · right; exact h
    · intro h
      cases h
      · exact hP_in
      · exact hQ_in

  exact hS_eq

-- ============================================================
-- Edge and welding definitions
-- ============================================================

def edge_of_triple (t : Triple) : ℕ × ℕ := (t.1, t.2.1)

def generator_available {n : ℕ} (P : Pedigree n) (t : Triple) : Prop :=
  let gen_layer := max 4 t.2.1
  ∃ g ∈ generators t, P.triple_at gen_layer = g

def condition1_weld {n : ℕ} (P Q : Pedigree n) (q : ℕ) (i : Bool) : Prop :=
  let t := if i then P.triple_at q else Q.triple_at q
  let other := if i then Q else P
  let (_, b, _) := t
  b > 3 ∧ ¬ generator_available other t ∧ b ∈ discords P Q

def condition2_weld {n : ℕ} (P Q : Pedigree n) (q : ℕ) (i : Bool) : Prop :=
  let t := if i then P.triple_at q else Q.triple_at q
  let e := edge_of_triple t
  let other := if i then Q else P
  ∃ s, s < q ∧ s ∈ discords P Q ∧ edge_of_triple (other.triple_at s) = e

def welded_to {n : ℕ} (P Q : Pedigree n) (q s : ℕ) : Prop :=
  s < q ∧ s ∈ discords P Q ∧ q ∈ discords P Q ∧
  ∃ i : Bool, condition1_weld P Q q i ∨ condition2_weld P Q q i

-- ============================================================
-- Graph of Rigidity
-- ============================================================

def rigidity_graph {n : ℕ} (P Q : Pedigree n) : SimpleGraph ℕ :=
  { Adj := fun s q => welded_to P Q q s }

-- ============================================================
-- Swap operation
-- ============================================================

def swap {n : ℕ} (P Q : Pedigree n) (C : Finset ℕ) : Pedigree n :=
  { triple_at := fun k => if k ∈ C then Q.triple_at k else P.triple_at k
    h3 := P.h3
    h_k_range := by
      intro k hk_ge hk_le
      simp only
      split_ifs
      · exact Q.h_k_range k hk_ge hk_le
      · exact P.h_k_range k hk_ge hk_le
    h_base := by
      have h3_not_in_C : 3 ∉ C := by
        intro hc
        simp [discords, mem_filter, mem_Ico] at hc
        linarith
      simp [h3_not_in_C, P.h_base]
    h_distinct := by
      -- Placeholder: will be proved when C is a component
      exact P.h_distinct }

-- ============================================================
-- Restrict pedigree to first k layers
-- ============================================================

def restrict {n : ℕ} (P : Pedigree n) (k : ℕ) (hk : 3 ≤ k ∧ k ≤ n) : Pedigree k :=
  { triple_at := P.triple_at
    h3 := hk.1
    h_k_range := by
      intro m hm hm'
      have hm_le : m ≤ k := by omega
      exact P.h_k_range m hm hm_le
    h_base := P.h_base
    h_distinct := by
      intro m1 m2 hm1 hm12 hm2
      have hm1' : 4 ≤ m1 := by omega
      have hm2' : m2 ≤ k := by omega
      exact P.h_distinct m1 m2 hm1' hm12 hm2' }

-- ============================================================
-- Helper: generator appears at correct layer in valid pedigree
-- ============================================================

lemma generator_at_correct_layer {n : ℕ} (P : Pedigree n) (k : ℕ) (hk : 4 ≤ k ∧ k ≤ n) :
    let t := P.triple_at k
    let (a, b, _) := t
    let gen_layer := max 4 b
    P.triple_at gen_layer ∈ generators t := by
  let t := P.triple_at k
  obtain ⟨a, b, hk_eq⟩ := t
  have h_b_lt_k : b < k := by
    obtain ⟨_, _, hb⟩ := mem_Delta_iff.mp (P.h_k_range k hk.1 hk.2)
    exact hb.2.1
  by_cases h_b_ge_4 : b ≥ 4
  · have h_gen : (a, b, b) ∈ generators (a, b, k) := by
      simp [generators, h_b_ge_4]
      left
      use a
      constructor
      · simp [h_b_ge_4]; omega
      · rfl
    have h_P_gen : P.triple_at b = (a, b, b) := by
      -- In a valid pedigree, the triple at layer b must be (a, b, b)
      -- because that's how the edge (a,b) was created
      have h_b_in_range : 3 ≤ b ∧ b ≤ n := by
        have h_b_ge_1 : 1 ≤ b := by
          obtain ⟨hb1, _, _⟩ := mem_Delta_iff.mp (P.h_k_range k hk.1 hk.2)
          exact hb1
        constructor
        · have h_b_ge_3 : 3 ≤ b := by omega
          exact h_b_ge_3
        · exact le_of_lt h_b_lt_k
      let t_b := P.triple_at b
      have h_t_b_mem : t_b ∈ Delta b := P.h_k_range b h_b_in_range.1 h_b_in_range.2
      obtain ⟨a', b', _⟩ := t_b
      have h_a'_eq : a' = a := by
        have h_edge : edge_of_triple t_b = (a, b) := by
          have h_gen_t_b : t_b ∈ generators (a, b, k) := by
            rw [← h_P_gen] at h_gen
            exact h_gen
          have h_t_b_gen := mem_generators_Delta (a, b, k) t_b (by omega) (by omega) h_gen_t_b
          simp [edge_of_triple] at h_t_b_gen ⊢
          exact h_t_b_gen
        exact h_edge.1
      have h_b'_eq : b' = b := by
        have h_edge : edge_of_triple t_b = (a, b) := by
          have h_gen_t_b : t_b ∈ generators (a, b, k) := by
            rw [← h_P_gen] at h_gen
            exact h_gen
          have h_t_b_gen := mem_generators_Delta (a, b, k) t_b (by omega) (by omega) h_gen_t_b
          simp [edge_of_triple] at h_t_b_gen ⊢
          exact h_t_b_gen
        exact h_edge.2
      rw [h_a'_eq, h_b'_eq]
    rw [h_P_gen]
    exact h_gen
  · have h_b_le_3 : b ≤ 3 := by omega
    have h_gen : (1, 2, 3) ∈ generators (a, b, k) := by
      simp [generators]
      rw [if_neg (by simp)]
      rw [if_neg (by omega)]
      simp
    have h_P_gen : P.triple_at 3 = (1, 2, 3) := P.h_base
    rw [← h_P_gen]
    exact h_gen

-- ============================================================
-- LEMMA 4.17: Singleton component swap valid
-- ============================================================

lemma singleton_swap_valid {n : ℕ} {P Q : Pedigree n} {l : ℕ}
    (h_comp : IsConnectedComponent (rigidity_graph P Q) {l}) :
    IsPedigree (swap P Q {l}) := by
  let Y := swap P Q {l}
  have h_l_discord : l ∈ discords P Q := by
    simp [IsConnectedComponent] at h_comp
    exact h_comp.1.1

  -- Part 1: Y/l is valid
  have h_restrict_valid : IsPedigree (restrict Y l ⟨by
      have h_l_ge : 4 ≤ l := by
        simp [mem_discords_iff] at h_l_discord
        exact h_l_discord.1
      exact ⟨h_l_ge, le_refl l⟩⟩) := by
    by_contra h_invalid
    -- Failure must be at layer l
    by_cases h_dup : ∃ k, 4 ≤ k ∧ k < l ∧ edge_of_triple (P.triple_at k) = edge_of_triple (Q.triple_at l)
    · obtain ⟨k, hk_ge, hk_lt, h_eq⟩ := h_dup
      have h_k_discord : k ∈ discords P Q := by
        by_contra h_not
        have h_agree : P.triple_at k = Q.triple_at k :=
          not_discord_agree P Q hk_ge (by omega) h_not
        rw [h_agree] at h_eq
        have h_diff : P.triple_at k ≠ Q.triple_at k := by
          simp [mem_discords_iff, hk_ge, hk_lt] at h_l_discord
          exact h_l_discord.2.2
        contradiction
      have h_weld : welded_to P Q l k := by
        refine ⟨hk_lt, h_k_discord, h_l_discord, ⟨false, Or.inr ⟨k, hk_lt, h_k_discord, h_eq⟩⟩⟩
      have h_k_in_C : k ∈ {l} := h_comp.2 k (by simp [h_k_discord]) (by simp [h_weld])
      simp at h_k_in_C
      subst h_k_in_C
      linarith
    · push_neg at h_dup
      let t := Q.triple_at l
      let (a, b, _) := t
      let gen_layer := max 4 b
      have h_gen_lt_l : gen_layer < l := by
        have h_b_lt_l : b < l := by
          obtain ⟨_, _, hb⟩ := mem_Delta_iff.mp (Q.h_k_range l (by omega) (by omega))
          exact hb.2.1
        by_cases h_b_ge_4 : b ≥ 4
        · exact h_b_lt_l
        · simp [gen_layer, h_b_ge_4]
          have h_l_ge_4 : 4 ≤ l := by
            simp [mem_discords_iff] at h_l_discord
            exact h_l_discord.1
          exact h_l_ge_4
      have h_gen_missing : P.triple_at gen_layer ∉ generators t := by
        -- This follows from invalidity of Y/l
        exact sorry
      have h_gen_discord : gen_layer ∈ discords P Q := by
        by_contra h_not
        have h_agree : P.triple_at gen_layer = Q.triple_at gen_layer :=
          not_discord_agree P Q (by omega) (by omega) h_not
        have h_Q_gen : Q.triple_at gen_layer ∈ generators t :=
          generator_at_correct_layer Q l ⟨by omega, by omega⟩
        rw [← h_agree] at h_Q_gen
        exact h_gen_missing h_Q_gen
      have h_weld : welded_to P Q l gen_layer := by
        refine ⟨h_gen_lt_l, h_gen_discord, h_l_discord, ⟨false, Or.inl ⟨b > 3, ?_, h_gen_discord⟩⟩⟩
        · have h_b_gt_3 : b > 3 := by
            have h_b_ge_4 : b ≥ 4 := by
              by_contra h_b_lt_4
              have h_b_le_3 : b ≤ 3 := by omega
              simp [gen_layer, h_b_le_3] at h_gen_lt_l
              linarith
            exact h_b_ge_4
          exact h_b_gt_3
        · exact h_gen_missing
      have h_gen_in_C : gen_layer ∈ {l} := h_comp.2 gen_layer (by simp [h_gen_discord]) (by simp [h_weld])
      simp at h_gen_in_C
      subst h_gen_in_C
      linarith

  -- Part 2: Extend to full n
  have h_full_valid : IsPedigree Y := by
    by_cases h_l_eq_n : l = n
    · exact h_restrict_valid
    · have h_valid_l : IsPedigree (restrict Y l ⟨by
          have h_l_ge : 4 ≤ l := by
            simp [mem_discords_iff] at h_l_discord
            exact h_l_discord.1
          exact ⟨h_l_ge, le_refl l⟩⟩) := h_restrict_valid
      have h_induct : ∀ q, l ≤ q → q ≤ n → IsPedigree (restrict Y q ⟨by
            have h_q_ge : 3 ≤ q := by omega
            exact ⟨h_q_ge, le_refl q⟩⟩) := by
        induction' q with q ih
        · intro h_le h_ge
          exact h_valid_l
        · intro hq_ge_l hq_lt_n
          have h_valid_q : IsPedigree (restrict Y q ⟨by omega, by omega⟩) :=
            ih (by omega) (by omega)
          let t := Y.triple_at (q+1)
          have h_ne_l : q+1 ≠ l := by omega
          have h_t_from_P : t = P.triple_at (q+1) := by
            simp [Y, swap, h_ne_l]
          let (a, b, _) := t
          let gen_layer := max 4 b
          have h_gen_available : ∃ g ∈ generators t, (restrict Y q ⟨by omega, by omega⟩).triple_at gen_layer = g := by
            have h_P_gen : P.triple_at gen_layer ∈ generators t :=
              generator_at_correct_layer P (q+1) ⟨by omega, by omega⟩
            by_cases h_gen_eq_l : gen_layer = l
            · have h_Q_gen : Q.triple_at l ∈ generators t := by
                -- Since l is not welded to q+1, generator is available in Q
                sorry
              have h_available : (restrict Y q ⟨by omega, by omega⟩).triple_at l = Q.triple_at l := by
                have h_l_le_q : l ≤ q := by
                  have h_b_lt : b < q+1 := by
                    obtain ⟨_, _, hb⟩ := mem_Delta_iff.mp (P.h_k_range (q+1) (by omega) (by omega))
                    exact hb.2.1
                  by_cases h_b_ge_4 : b ≥ 4
                  · have h_gen : gen_layer = b := by simp [gen_layer, h_b_ge_4]
                    rw [← h_gen_eq_l] at h_gen
                    omega
                  · simp [gen_layer, h_b_ge_4]
                    have h_l_ge_4 : 4 ≤ l := by
                      simp [mem_discords_iff] at h_l_discord
                      exact h_l_discord.1
                    omega
                simp [restrict, Y, swap, h_l_le_q]
              exact ⟨Q.triple_at l, h_Q_gen, h_available⟩
            · have h_available : (restrict Y q ⟨by omega, by omega⟩).triple_at gen_layer = P.triple_at gen_layer := by
                have h_gen_le_q : gen_layer ≤ q := by
                  have h_b_lt : b < q+1 := by
                    obtain ⟨_, _, hb⟩ := mem_Delta_iff.mp (P.h_k_range (q+1) (by omega) (by omega))
                    exact hb.2.1
                  by_cases h_b_ge_4 : b ≥ 4
                  · exact h_b_lt
                  · simp [gen_layer, h_b_ge_4]
                    have h_l_ge_4 : 4 ≤ l := by
                      simp [mem_discords_iff] at h_l_discord
                      exact h_l_discord.1
                    exact h_l_ge_4
                simp [restrict, Y, swap, h_gen_eq_l, h_gen_le_q]
              exact ⟨P.triple_at gen_layer, h_P_gen, h_available⟩
          have h_distinct : ∀ k, 4 ≤ k → k ≤ q → (restrict Y q ⟨by omega, by omega⟩).triple_at k ≠ t := by
            intro k hk_ge hk_le
            by_contra h_eq
            by_cases hk_eq_l : k = l
            · have h_weld : welded_to P Q (q+1) l := by
                have h_eq_edge : edge_of_triple (Q.triple_at l) = edge_of_triple (P.triple_at (q+1)) := by
                  simp [restrict, Y, swap, hk_eq_l] at h_eq
                  simp [h_t_from_P] at h_eq
                  exact h_eq
                refine ⟨l, by omega, h_l_discord, ?_, ⟨true, Or.inr ⟨l, by omega, h_l_discord, h_eq_edge⟩⟩⟩
                exact (mem_discords_iff P Q).mpr ⟨4 ≤ q+1, q+1 ≤ n, by
                  have h_diff : P.triple_at (q+1) ≠ Q.triple_at (q+1) := by
                    rw [← mem_discords_iff]
                    have h_q1_gt_l : q+1 > l := by omega
                    have h_q1_not_discord : q+1 ∉ discords P Q := by
                      intro h_contra
                      have h_contra_mem : q+1 ∈ {l} := h_comp.2 (q+1) (by simp [h_contra]) (by simp [h_weld])
                      simp at h_contra_mem
                      linarith
                    simp [mem_discords_iff, h_q1_gt_l, h_q1_not_discord]
                  exact h_diff⟩
              have h_q1_in_C : q+1 ∈ {l} := h_comp.2 (q+1) (by
                  simp [mem_discords_iff]
                  refine ⟨4 ≤ q+1, q+1 ≤ n, ?_⟩
                  intro h_eq
                  rw [h_eq] at h_weld
                  exact h_weld.2.2.2.1) (by simp [h_weld])
              simp at h_q1_in_C
              linarith
            · have h_t_k : (restrict Y q ⟨by omega, by omega⟩).triple_at k = P.triple_at k := by
                simp [restrict, Y, swap, hk_eq_l, hk_le]
              rw [h_t_k, h_t_from_P] at h_eq
              exact P.h_distinct k (q+1) (by omega) (by omega) (by omega) h_eq
          exact IsPedigree.extend h_valid_q t h_gen_available h_distinct
      exact h_induct n (by omega) (by omega)

  exact h_full_valid

-- ============================================================
-- THEOREM 4.19: Swapping a component yields a valid pedigree
-- ============================================================

theorem component_swap_valid {n : ℕ} (P Q : Pedigree n) (C : Finset ℕ)
    (h_comp : IsConnectedComponent (rigidity_graph P Q) C) :
    IsPedigree (swap P Q C) := by
  induction' C using Finset.strongInduction with C ih
  by_cases h_card : card C = 1
  · exact singleton_swap_valid P Q (by
      have h_singleton : ∃ l, C = {l} := card_eq_one.mp h_card
      obtain ⟨l, h_eq⟩ := h_singleton
      rw [h_eq] at h_comp
      exact h_comp)
  · -- Inductive step: |C| > 1
    have h_nonempty : C.Nonempty := by
      rw [← card_pos, ← h_card]
      simp; omega
    let l := max' C h_nonempty
    have hl_in : l ∈ C := max'_mem C h_nonempty
    let C' := C \ {l}
    have hC'_card : card C' = card C - 1 := by simp [C']
    have hC'_lt : card C' < card C := by omega

    -- l must be welded to some s in C'
    obtain ⟨s, hs_in, hs_lt, h_weld⟩ : ∃ s ∈ C', s < l ∧ welded_to P Q l s := by
      sorry

    -- By induction, swapping C' is valid (C' is a union of components, each smaller)
    have h_swap_C' : IsPedigree (swap P Q C') := by
      sorry

    -- Add back l using the weld to s
    have h_swap_C : IsPedigree (swap P Q C) := by
      sorry

    exact h_swap_C

-- ============================================================
-- MAIN THEOREM 4.18: Adjacent iff G_R connected
-- ============================================================

theorem adjacency_iff_rigidity_graph_connected {n : ℕ} (P Q : Pedigree n) :
    AdjacentInPolytope P Q ↔ (rigidity_graph P Q).Connected := by
  constructor
  · intro h_adj
    by_contra h_disconn
    sorry
  · intro h_conn
    by_cases h_single : card (discords P Q) = 1
    · exact adjacent_if_single_discord P Q h_single
    · sorry

end MembershipProject.Core
