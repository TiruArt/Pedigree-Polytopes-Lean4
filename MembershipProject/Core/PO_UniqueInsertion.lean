import MembershipProject.Core.PO_BasicDefinitions
import Mathlib.Tactic

namespace PedigreeOpt

open Finset
open scoped BigOperators

structure MIR (n : ℕ) where
  x : (k : Fin n) → (Fin n × Fin n × Fin n) → ℝ
  u : Sym2 (Fin n) → ℝ
  eq6 : ∀ (k : Fin n) (_hk : k.1 ≥ 3), (∑ t ∈ DeltaK n k, x k t) = 1
  eq7 : ∀ (i j : Fin n), i < j →
    (∑ k ∈ Icc 4 n,
      if h_bound : k < n then
        ∑ t ∈ DeltaK n ⟨k, h_bound⟩, if commonEdge t = (i, j) then x ⟨k, h_bound⟩ t else 0
      else 0) + u (Sym2.mk i j) = 1
  nonneg : ∀ k t, x k t ≥ 0
  u_nonneg : ∀ e, u e ≥ 0
structure IntegerMIR (n : ℕ) extends MIR n where
  binary : ∀ k t, x k t = 0 ∨ x k t = 1

theorem unique_insertion (n : ℕ) (k : Fin n) (hk : k.1 ≥ 3) (X : IntegerMIR n) :
    ∃! t, t ∈ DeltaK n k ∧ X.x k t = 1 := by
  let S := DeltaK n k
  have h_sum := X.eq6 k hk
  -- 1. Existence
  have ex : ∃ t ∈ S, X.x k t = 1 := by
    by_contra! h
    have all_zero : ∀ t ∈ S, X.x k t = 0 := by
      intro t ht
      cases X.binary k t with

      | inl h0 => exact h0
      | inr h1 => exfalso; exact h t ht h1
    rw [sum_congr rfl all_zero, sum_const_zero] at h_sum
    linarith
  -- 2. Uniqueness
  obtain ⟨t, ht_mem, ht_val⟩ := ex
  refine ⟨t, ⟨ht_mem, ht_val⟩, λ u_tri ⟨hu_mem, hu_val⟩ => ?_⟩
  by_contra h_ne
  -- We need to prove the sum of the pair is 2
  have h_pair : ∑ v ∈ ({t, u_tri} : Finset (Fin n × Fin n × Fin n)), X.x k v = 2 := by
    -- Use Ne.symm h_ne to match the expectation t ∉ {u_tri}
    rw [sum_insert (show t ∉ {u_tri} by simp [Ne.symm h_ne]), sum_singleton, ht_val, hu_val]
    norm_num
  -- Use the non-negative version of the subset sum lemma
  have h_le : ∑ v ∈ ({t, u_tri} : Finset (Fin n × Fin n × Fin n)), X.x k v ≤ ∑ v ∈ S, X.x k v := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro v; simp; intro h_ext; cases h_ext <;> subst v <;> assumption
    · intro v _ _; apply X.nonneg
  rw [h_pair, h_sum] at h_le
  linarith

end PedigreeOpt
