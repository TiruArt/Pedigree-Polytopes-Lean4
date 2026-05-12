import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open BigOperators

namespace UniqueInsertion

def Triangle (n : ℕ) := Fin n × Fin n × Fin n

instance (n : ℕ) : Fintype (Triangle n) := by unfold Triangle; infer_instance
instance (n : ℕ) : DecidableEq (Triangle n) := by unfold Triangle; infer_instance

def triangles_at_k (n : ℕ) (k : Fin n) : Finset (Triangle n) :=
  Finset.filter (λ t => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 = k) Finset.univ

structure MIR (n : ℕ) where
  x : Triangle n → ℝ
  eq6 : ∀ (k : Fin n) (_ : k.1 ≥ 3), ∑ t ∈ triangles_at_k n k, x t = 1
  nonneg : ∀ t, x t ≥ 0

structure IntegerMIR (n : ℕ) extends MIR n where
  binary : ∀ t, x t = 0 ∨ x t = 1

theorem unique_insertion_sequence (n : ℕ) (k : Fin n) (hk : k.1 ≥ 3) (X : IntegerMIR n) :
    ∃! (t : Triangle n), t ∈ triangles_at_k n k ∧ X.x t = 1 := by
  let S := triangles_at_k n k
  have ex : ∃ t ∈ S, X.x t = 1 := by
    by_contra! h
    have all_zero : ∀ t ∈ S, X.x t = 0 := λ t ht => (X.binary t).resolve_right (h t ht)
    have sum_val : ∑ t ∈ S, X.x t = 1 := X.eq6 k hk
    rw [Finset.sum_congr rfl all_zero] at sum_val
    rw [Finset.sum_const_zero] at sum_val
    linarith
  obtain ⟨t, ht⟩ := ex
  refine ⟨t, ht, λ u ⟨hu, hu_val⟩ => ?_⟩
  by_contra hne
  have h : t ≠ u := Ne.symm hne
  have subset : {t, u} ⊆ S := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    obtain (h1 | h2) := hv
    · rw [h1]; exact ht.1
    · rw [h2]; exact hu
  have le_sum : ∑ v ∈ {t, u}, X.x v ≤ ∑ v ∈ S, X.x v :=
    Finset.sum_le_sum_of_subset_of_nonneg subset (λ v _ _ => X.nonneg v)
  have sum_pair : ∑ v ∈ {t, u}, X.x v = X.x t + X.x u :=
    Finset.sum_pair h
  rw [sum_pair, X.eq6 k hk] at le_sum
  rw [ht.2, hu_val] at le_sum
  linarith

end UniqueInsertion
