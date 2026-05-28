import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Mathlib.Data.List.Nodup
open Finset

abbrev Triple := ℕ × ℕ × ℕ

namespace Triple
abbrev i (t : Triple) : ℕ := t.1
abbrev j (t : Triple) : ℕ := t.2.1
abbrev k (t : Triple) : ℕ := t.2.2
def toFinset (t : Triple) : Finset ℕ := {t.i, t.j, t.k}
end Triple

opaque generators : Triple → Finset Triple

def Delta (l : ℕ) : Finset Triple :=
  (Finset.Ico 1 l ×ˢ (Finset.Ico 1 l ×ˢ ({l} : Finset ℕ))).filter
    fun t => t.1 < t.2.1

def isPreSolution (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  S.card = n - 2 ∧
  (∀ t ∈ S, t.card = 3) ∧
  (∀ k ∈ Finset.Icc 3 n, ∃ t ∈ S, (k ∈ t ∧ ∀ x ∈ t, x ≤ k) ∧
    ∀ t' ∈ S, (k ∈ t' ∧ ∀ x ∈ t', x ≤ k) → t' = t)

structure Pedigree (n : ℕ) where
  triangles  : List Triple
  h_n        : 3 ≤ n
  h_length   : triangles.length = n - 2
  h_first    : triangles.head? = some (1, 2, 3)
  h_layers   : ∀ i, ∀ hi : i < triangles.length,
                 (triangles.get ⟨i, hi⟩).k = i + 3
  h_generators : ∀ i, i > 0 → ∀ hi : i < triangles.length,
                   ∃ j, ∃ hj : j < i,
                     (triangles.get ⟨j, Nat.lt_trans hj hi⟩) ∈
                       generators (triangles.get ⟨i, hi⟩)
  h_distinct : ∀ i j,
                 ∀ hi : i < triangles.length,
                 ∀ hj : j < triangles.length,
                 i > 0 → j > 0 → i ≠ j →
                 ((triangles.get ⟨i, hi⟩).i, (triangles.get ⟨i, hi⟩).j) ≠
                 ((triangles.get ⟨j, hj⟩).i, (triangles.get ⟨j, hj⟩).j)
  h_in_delta : ∀ i, ∀ hi : i < triangles.length,
                 (triangles.get ⟨i, hi⟩) ∈ Delta (triangles.get ⟨i, hi⟩).k

def pedigreeListToFinset (triangles : List Triple) : Finset (Finset ℕ) :=
  (triangles.map Triple.toFinset).toFinset

lemma triple_max_eq_k {n : ℕ} (p : Pedigree n) (idx : ℕ) (hidx : idx < p.triangles.length) :
  (p.triangles.get ⟨idx, hidx⟩).toFinset.max = some ((p.triangles.get ⟨idx, hidx⟩).k) := by
  have h_delta := p.h_in_delta idx hidx
  generalize h_t : p.triangles.get ⟨idx, hidx⟩ = t at *
  unfold Delta at h_delta
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_singleton] at h_delta
  rcases h_delta with ⟨⟨hi_ico, hj_ico, hk_sing⟩, h_ij_lt⟩
  rw [Finset.mem_Ico] at hi_ico hj_ico
  have h_i_lt_k : t.1 < t.2.2 := by omega
  have h_j_lt_k : t.2.1 < t.2.2 := by omega
  let s := t.toFinset
  let k := t.k
  cases h_max : s.max with


  | bot =>
    have hk_mem : k ∈ s := by simp [s, Triple.toFinset, k]
    have h_emp := Finset.max_eq_bot.mp h_max
    rw [h_emp] at hk_mem
    simp at hk_mem
  | coe m =>
    congr
    have hm_mem := Finset.mem_of_max h_max
    have hk_mem : k ∈ s := by simp [s, Triple.toFinset, k]
    simp [s, Triple.toFinset, Triple.i, Triple.j, Triple.k] at hm_mem
    have hm_le_k : m ≤ k := by
      rcases hm_mem with hm | hm | hm
      · rw [hm]; omega
      · rw [hm]; omega
      · rw [hm]
    have hk_le_m : k ≤ m := by
      have h_le := Finset.le_max hk_mem
      rw [h_max] at h_le
      exact WithBot.coe_le_coe.mp h_le
    omega

lemma pedigree_list_to_isPreSolution_layers {n : ℕ} (p : Pedigree n) :
  ∀ k ∈ Finset.Icc 3 n, ∃ t ∈ pedigreeListToFinset p.triangles,
    (k ∈ t ∧ ∀ x ∈ t, x ≤ k) ∧
    ∀ t' ∈ pedigreeListToFinset p.triangles, (k ∈ t' ∧ ∀ x ∈ t', x ≤ k) → t' = t := by
  intro k hk
  rw [Finset.mem_Icc] at hk
  have hk_min : 3 ≤ k := hk.1
  have hk_max : k ≤ n := hk.2
  let idx := k - 3
  have h_idx_lt : idx < p.triangles.length := by have h_len := p.h_length; omega
  let target_triple := p.triangles.get ⟨idx, h_idx_lt⟩
  let t_witness := target_triple.toFinset
  have h_layer_eq := p.h_layers idx h_idx_lt
  have h_max_wit : t_witness.max = some k := by
    have h_max := triple_max_eq_k p idx h_idx_lt
    rw [h_max]; congr; omega
  have h_prop_wit : k ∈ t_witness ∧ ∀ x ∈ t_witness, x ≤ k := by
    constructor
    · exact Finset.mem_of_max h_max_wit
    · intro x hx
      have h_le := Finset.le_max hx
      rw [h_max_wit] at h_le
      exact WithBot.coe_le_coe.mp h_le
  use t_witness
  constructor
  · simp only [pedigreeListToFinset, List.mem_toFinset, List.mem_map]
    use target_triple; constructor
    · exact List.get_mem p.triangles ⟨idx, h_idx_lt⟩
    · rfl
  · constructor
    · exact h_prop_wit
    · intro t' ht' h_prop'
      have hk_in_t' := h_prop'.1
      have h_le_k' := h_prop'.2
      have h_max_t' : t'.max = some k := by
        have h_is_max : k ∈ t' := hk_in_t'
        have h_is_ub : ∀ x ∈ t', x ≤ k := h_le_k'
        cases h_eq : t'.max with


        | bot =>
          have h_emp := Finset.max_eq_bot.mp h_eq
          rw [h_emp] at hk_in_t'
          simp at hk_in_t'
        | coe m =>
          have h_mem_m := Finset.mem_of_max h_eq
          have h_le := h_is_ub m h_mem_m
          have h_ge_withbot := Finset.le_max hk_in_t'
          rw [h_eq] at h_ge_withbot
          have h_ge := WithBot.coe_le_coe.mp h_ge_withbot
          have h_m_eq : m = k := by omega
          subst h_m_eq; rfl
      simp only [pedigreeListToFinset, List.mem_toFinset, List.mem_map] at ht'
      rcases ht' with ⟨triple_j, h_mem_j, rfl⟩
      rcases List.mem_iff_get.mp h_mem_j with ⟨⟨j, hj_lt⟩, h_get_j⟩
      have h_max_j := triple_max_eq_k p j hj_lt
      have h_triple_j_eq : p.triangles.get ⟨j, hj_lt⟩ = triple_j := h_get_j
      have h_max_t_copy := h_max_t'
      rw [← h_triple_j_eq] at h_max_t'
      rw [h_max_j] at h_max_t'
      injection h_max_t' with hk_match
      have h_layer_j := p.h_layers j hj_lt
      have h_idx_eq_j : idx = j := by omega
      rcases h_idx_eq_j with rfl
      dsimp [t_witness, target_triple]
      rw [← h_triple_j_eq]; congr

lemma pedigree_triangles_card3 {n : ℕ} (p : Pedigree n) (t_init : Triple) (ht : t_init ∈ p.triangles) :
  t_init.toFinset.card = 3 := by
  rcases List.mem_iff_get.mp ht with ⟨⟨idx, hidx⟩, h_eq⟩
  have h_delta := p.h_in_delta idx hidx
  generalize h_t : p.triangles.get ⟨idx, hidx⟩ = t at *
  unfold Delta at h_delta
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_singleton] at h_delta
  rcases h_delta with ⟨⟨hi_ico, hj_ico, hk_sing⟩, h_ij_lt⟩
  rw [Finset.mem_Ico] at hi_ico hj_ico
  subst h_eq; simp [Triple.toFinset, Triple.i, Triple.j, Triple.k]
  have h1 : t.1 ≠ t.2.1 := by omega
  have h2 : t.2.1 ≠ t.2.2 := by omega
  have h3 : t.1 ≠ t.2.2 := by omega
  rw [Finset.card_eq_three]
  use t.1, t.2.1, t.2.2

lemma triangles_nodup {n : ℕ} (p : Pedigree n) : p.triangles.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j h_eq

  by_contra h_neq
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  dsimp at h_eq

  have h_triple_eq : p.triangles.get ⟨i, hi⟩ = p.triangles.get ⟨j, hj⟩ := h_eq
  have h_idx_neq : i ≠ j := by
    intro h_c; exact h_neq (by ext; exact h_c)

  rcases (Nat.eq_zero_or_pos i) with hi0 | hi_pos
  · subst hi0
    have h_j_gt : j > 0 := by omega
    have hk_zero := p.h_layers 0 hi
    have hk_j := p.h_layers j hj
    have hk_eq : (p.triangles.get ⟨0, hi⟩).k = (p.triangles.get ⟨j, hj⟩).k := by
      rw [h_triple_eq]
    rw [hk_zero, hk_j] at hk_eq
    omega
  · rcases (Nat.eq_zero_or_pos j) with hj0 | hj_pos
    · subst hj0
      have h_i_gt : i > 0 := by omega
      have hk_i := p.h_layers i hi
      have hk_zero := p.h_layers 0 hj
      have hk_eq : (p.triangles.get ⟨i, hi⟩).k = (p.triangles.get ⟨0, hj⟩).k := by
        rw [h_triple_eq]
      rw [hk_i, hk_zero] at hk_eq
      omega
    · have h_distinct_violation := p.h_distinct i j hi hj hi_pos hj_pos h_idx_neq
      have h_ij_eq : ((p.triangles.get ⟨i, hi⟩).i, (p.triangles.get ⟨i, hi⟩).j) =
                     ((p.triangles.get ⟨j, hj⟩).i, (p.triangles.get ⟨j, hj⟩).j) := by
        rw [h_triple_eq]
      exact h_distinct_violation h_ij_eq

theorem pedigree_to_isPreSolution {n : ℕ} (p : Pedigree n) :
  isPreSolution n (pedigreeListToFinset p.triangles) := by
  unfold isPreSolution
  refine ⟨?_card, ?_card3, ?_layers⟩
  · -- 1. Cardinality verification: S.card = n - 2
    unfold pedigreeListToFinset
    rw [List.toFinset_card_of_nodup]
    · rw [List.length_map, p.h_length]
    · rw [List.nodup_iff_injective_get]
      intro i j h_eq
      rcases i with ⟨i, hi⟩
      rcases j with ⟨j, hj⟩
      dsimp at h_eq

      have h_len : (p.triangles.map Triple.toFinset).length = p.triangles.length := List.length_map Triple.toFinset
      have hi' : i < p.triangles.length := by omega
      have hj' : j < p.triangles.length := by omega

      -- DEFINITIVE FIX: Instead of calling an unknown lemma, we use general structural
      -- equalities to unwrap the mapped list elements natively without external constants
      have h_get_i : (p.triangles.map Triple.toFinset).get ⟨i, hi⟩ = (p.triangles.get ⟨i, hi'⟩).toFinset := by
        generalize h_lookup : p.triangles.get ⟨i, hi'⟩ = t
        simp [← h_lookup]
      have h_get_j : (p.triangles.map Triple.toFinset).get ⟨j, hj⟩ = (p.triangles.get ⟨j, hj'⟩).toFinset := by
        generalize h_lookup : p.triangles.get ⟨j, hj'⟩ = t
        simp [← h_lookup]

      rw [h_get_i, h_get_j] at h_eq

      have h_max_i := triple_max_eq_k p i hi'
      have h_max_j := triple_max_eq_k p j hj'

      rw [h_eq] at h_max_i
      rw [h_max_i] at h_max_j
      injection h_max_j with hk_eq
      have h_layer_i := p.h_layers i hi'
      have h_layer_j := p.h_layers j hj'
      have h_idx_eq : i = j := by omega
      apply Fin.ext
      exact h_idx_eq

  · -- 2. Triangle Element Size: ∀ t ∈ S, t.card = 3
    intro t ht
    simp only [pedigreeListToFinset, List.mem_toFinset, List.mem_map] at ht
    rcases ht with ⟨triple_witness, h_mem, h_set_eq⟩
    subst h_set_eq
    exact pedigree_triangles_card3 p triple_witness h_mem

  · -- 3. Layer Unicity and Existence
    exact pedigree_list_to_isPreSolution_layers p
