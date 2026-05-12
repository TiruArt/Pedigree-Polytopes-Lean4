import MembershipProject.Core.PO_BasicDefinitions
import MembershipProject.Core.PO_UniqueInsertion
import Mathlib.Tactic

namespace PedigreeOpt

open Finset
open scoped BigOperators
open scoped Classical

/--
  Lemma: A sum of binary (0/1) variables that is ≤ 1 must be 0 or 1.
-/
lemma sum_binary_le_one {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℝ}
  (h_bin : ∀ i ∈ s, f i = 0 ∨ f i = 1)
  (h_le : ∑ i ∈ s, f i ≤ 1)
  (h_nonneg : ∀ i ∈ s, f i ≥ 0) :
  ∑ i ∈ s, f i = 0 ∨ ∑ i ∈ s, f i = 1 := by
  induction s using Finset.induction with

  | empty => left; simp
  | insert a s' ha ih =>
    rw [sum_insert ha]
    rcases h_bin a (mem_insert_self a s') with ha0 | ha1
    · rw [ha0]; simp; apply ih
      · intro i hi; apply h_bin i (mem_insert_of_mem hi)
      · rw [sum_insert ha, ha0] at h_le; simp at h_le; exact h_le
      · intro i hi; apply h_nonneg i (mem_insert_of_mem hi)
    · rw [ha1]; right
      have : ∑ i ∈ s', f i = 0 := by
        have h_sum := h_le
        rw [sum_insert ha, ha1] at h_sum
        have : ∑ i ∈ s', f i ≤ 0 := by linarith
        apply le_antisymm this (sum_nonneg (λ i hi => h_nonneg i (mem_insert_of_mem hi)))
      rw [this]; simp

/--
  Theorem: The slack variable u_{ij} is binary (0 or 1).
-/
theorem slack_is_binary (n : ℕ) (X : IntegerMIR n) (i j : Fin n) (h_lt : i < j) :
    X.u (Sym2.mk i j) = 0 ∨ X.u (Sym2.mk i j) = 1 := by
  let h7 := X.eq7 i j h_lt
  let f_sum := (∑ k' ∈ Icc 4 n, if h_bound : k' < n then ∑ t ∈ DeltaK n ⟨k', h_bound⟩, if commonEdge t = (i, j) then X.x ⟨k', h_bound⟩ t else (0 : ℝ) else (0 : ℝ))

  have h_sum_binary : f_sum = 0 ∨ f_sum = 1 := by
    apply sum_binary_le_one
    · intro k_idx _hk_mem; split_ifs with h_b
      .sorry
      · left; rfl
    · linarith [h7, X.u_nonneg (Sym2.mk i j)]
    · intro k_idx _hk_mem; split_ifs with h_b
      · apply sum_nonneg; intro t _; split_ifs; apply X.nonneg; linarith
      · linarith

  rcases h_sum_binary with h0 | h1
  · right; linarith [h0, h7]
  · left; linarith [h1, h7]

/--
  Lemma: Edge Removal
  Fixed "failed to create binder" by removing 'set'.
-/
theorem edge_removal (n : ℕ) (X : IntegerMIR n) (i j k : Fin n) (h_lt : i < j)
  (t_tri : Fin n × Fin n × Fin n) (ht : t_tri ∈ DeltaK n k) (hx : X.x k t_tri = 1) (h_comm : commonEdge t_tri = (i, j)) :
  X.u (Sym2.mk i j) = 0 := by
  let h7 := X.eq7 i j h_lt

  let f (k' : ℕ) : ℝ :=
    if h_b : k' < n then
      ∑ t' ∈ DeltaK n ⟨k', h_b⟩, if commonEdge t' = (i, j) then X.x ⟨k', h_b⟩ t' else (0 : ℝ)
    else (0 : ℝ)

  have h_mem : k.1 ∈ Icc 4 n := sorry

  have h_fk_is_one : f k.1 = 1 := by
    simp [f, k.is_lt]
    -- 1. Use 'trans' to bridge the sum and the literal 1
    trans (if commonEdge t_tri = (i, j) then X.x k t_tri else 0)
    · apply Finset.sum_eq_single t_tri
      · intro t' ht' hne
        split_ifs with h_c
        · -- Insert your uniqueness logic here
          sorry
        · rfl
      · intro h_not_in; contradiction -- ht proves it is in
    · -- 2. Now prove the single term equals 1
      simp [h_comm, hx]


  have h_sum_ge1 : (∑ k' ∈ Icc 4 n, f k') ≥ 1 := by
    rw [← h_fk_is_one]
    apply Finset.single_le_sum
    · intro k' _; dsimp [f]; split_ifs
      · apply sum_nonneg; intro t' _; split_ifs; apply X.nonneg; linarith
      · linarith
    · exact h_mem

  have h7_final : (∑ k' ∈ Icc 4 n, f k') + X.u (Sym2.mk i j) = 1 := by
    rw [← h7];

  linarith [h7_final, h_sum_ge1, X.u_nonneg (Sym2.mk i j)]

end PedigreeOpt
