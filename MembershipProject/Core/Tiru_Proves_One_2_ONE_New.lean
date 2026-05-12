import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open BigOperators

namespace PedigreeOptimization

/-- All triples (i, j, k) with i, j, k ∈ Fin n and i < j < k. -/
def triangle_set (n : ℕ) : Finset (Fin n × Fin n × Fin n) :=
  Finset.filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2) Finset.univ

/-- Triples with a fixed k (k must be ≥ 3 in the intended use). -/
def triangles_at_k (n : ℕ) (k : Fin n) : Finset (Fin n × Fin n × Fin n) :=
  Finset.filter (fun t => t.2.2 = k) (triangle_set n)

/-- MIR(n): linear relaxation of the pedigree optimisation problem. -/
structure MIR (n : ℕ) where
  x : (Fin n × Fin n × Fin n) → ℝ
  eq6 : ∀ (k : Fin n) (_ : k.1 ≥ 3), ∑ t in triangles_at_k n k, x t = 1
  nonneg : ∀ t, x t ≥ 0

/-- Integer solution to MIR(n): x_t ∈ {0,1}. -/
structure IntegerMIR (n : ℕ) extends MIR n where
  binary : ∀ t, x t = 0 ∨ x t = 1

/-- If a sum of binary non‑negative numbers equals 1, exactly one of them is 1. -/
lemma sum_binary_eq_one_implies_unique_one {α : Type*} [Fintype α] (f : α → ℝ)
    (h0 : ∀ a, f a ≥ 0) (hbin : ∀ a, f a = 0 ∨ f a = 1) (hsum : ∑ a, f a = 1) :
    ∃! a, f a = 1 := by
  -- existence
  have ex : ∃ a, f a = 1 := by
    by_contra! h
    have : ∀ a, f a = 0 := λ a => (hbin a).resolve_right (h a)
    simp [this] at hsum
    contradiction
  obtain ⟨a, ha⟩ := ex
  -- uniqueness
  refine ⟨a, ha, λ b hb => ?_⟩
  by_contra hne
  let S := Finset.cons a (Finset.cons b ∅ (by simp)) (by simp) (by simp [hne])
  have hsub : S ⊆ Finset.univ := by simp
  have le_sum : ∑ x in S, f x ≤ ∑ x, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (λ x _ => h0 x)
  have sum_S : ∑ x in S, f x = f a + f b := by
    simp [S, ha, hb]
    rfl
  rw [sum_S] at le_sum
  linarith [hsum]

/-- From eq6 and binary property, for each k there is a unique triangle (i,j,k) with x = 1. -/
theorem unique_insertion_sequence {n : ℕ} (X : IntegerMIR n) (k : Fin n) (hk : k.1 ≥ 3) :
    ∃! (t : Fin n × Fin n × Fin n), t ∈ triangles_at_k n k ∧ X.x t = 1 := by
  let S := triangles_at_k n k
  let f : S → ℝ := λ s => X.x s.val
  have hsum : ∑ s : S, f s = 1 := by
    convert X.eq6 k hk
    · ext t; simp [f]
    · rw [Finset.sum_attach]
  have h0 : ∀ s : S, f s ≥ 0 := λ s => X.nonneg s.val
  have hbin : ∀ s : S, f s = 0 ∨ f s = 1 := λ s => X.binary s.val
  obtain ⟨s, hs, huniq⟩ := sum_binary_eq_one_implies_unique_one f h0 hbin hsum
  refine ⟨s.val, ⟨s.property, hs⟩, ?_⟩
  intro t ⟨ht_mem, ht_val⟩
  have t' : S := ⟨t, ht_mem⟩
  have ht'_val : f t' = 1 := by simp [f, ht_val]
  have eq : t' = s := huniq t' ht'_val
  exact congr_arg (λ (x : S) => x.val) eq

end PedigreeOptimization
