import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open Finset
open BigOperators

-- Universal variables setup
variable {D : Type*} [DecidableEq D] [Fintype D]

-- Map subsets correctly: Index Set comes first, then the mapping function
def g_set (S : Finset D) (g : D → ℚ) : ℚ := ∑ d ∈ S, g d

-- Structural definition of a partition inside Lean 4
structure IsPartition (P : Finset (Finset D)) : Prop where
  disjoint : ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B
  cover    : Finset.bUnion P id = univ

-- Full Theorem: Proves Nonnegativity, Destination Demand, and Origin Supply Constraints
theorem fat_feasible
    (g : D → ℚ)
    (hg_nonneg : ∀ d, g d ≥ 0)
    (D1 D2 : Finset (Finset D))
    (hD1 : IsPartition D1)
    (hD2 : IsPartition D2)
    (α : Finset D) (hα : α ∈ D1)
    (β : Finset D) (hβ : β ∈ D2) :
    -- 1. Nonnegativity constraint: f_αβ >= 0
    g_set (α ∩ β) g ≥ 0 ∧
    -- 2. Demand constraint: summing flows over origins meets destination demand (b_β)
    (∑ A ∈ D1, g_set (A ∩ β) g = g_set β g) ∧
    -- 3. Supply constraint: summing flows over destinations equals origin supply (a_α)
    (∑ B ∈ D2, g_set (α ∩ B) g = g_set α g) := by
  refine ⟨?_, ?_, ?_⟩
  · -- --- PART 1: Nonnegativity Verification ---
    dsimp [g_set]
    exact Finset.sum_nonneg (fun d _ => hg_nonneg d)
  · -- --- PART 2: Demand Balance Constraints ---
    dsimp [g_set]
    rw [← Finset.sum_bUnion]
    · congr 1
      ext x
      simp only [Finset.mem_bUnion, Finset.mem_inter, id_eq]
      constructor
      · rintro ⟨A, _, hAx, hβx⟩
        exact hβx
      · intro hβx
        have h_univ : x ∈ univ := Finset.mem_univ x
        rw [← hD1.cover] at h_univ
        rw [Finset.mem_bUnion] at h_univ
        rcases h_univ with ⟨A, hA, hAx⟩
        exact ⟨A, hA, hAx, hβx⟩
    · intro A hA B hB hne
      exact Disjoint.mono (Finset.inter_subset_left A β) (Finset.inter_subset_left B β) (hD1.disjoint A hA B hB hne)
  · -- --- PART 3: Supply Balance Constraints (Symmetric Proof) ---
    dsimp [g_set]
    rw [← Finset.sum_bUnion]
    · congr 1
      ext x
      simp only [Finset.mem_bUnion, Finset.mem_inter, id_eq]
      constructor
      · rintro ⟨B, _, hαx, hBx⟩
        exact hαx
      · intro hαx
        have h_univ : x ∈ univ := Finset.mem_univ x
        rw [← hD2.cover] at h_univ
        rw [mem_bUnion] at h_univ
        rcases h_univ with ⟨B, hB, hBx⟩
        exact ⟨B, hB, hαx, hBx⟩
    · intro A hA B hB hne
      exact Disjoint.mono (Finset.inter_subset_right α A) (Finset.inter_subset_right α B) (hD2.disjoint A hA B hB hne)
