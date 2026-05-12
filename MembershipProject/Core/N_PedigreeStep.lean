-- N_PedigreeStep.lean
-- Inductive step: Pedigree (k-1) S → Pedigree k (S ∪ {{i,j,k}})

import MembershipProject.Core.LearningFinsetDesirableDef
import Mathlib.Tactic

namespace MembershipProject.Core

open Finset

-- Helper: max of {i,j,k} with i < j < k is k
lemma max_triple (i j k : ℕ) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    ({i, j, k} : Finset ℕ).max = some k := by
  rw [Finset.max_insert, Finset.max_insert, Finset.max_singleton]
  simp [Finset.sup_eq_max]
  omega

-- Helper: {i,j,k}.card = 3 when i < j < k
lemma card_triple (i j k : ℕ) (hij : i < j) (hjk : j < k) :
    ({i, j, k} : Finset ℕ).card = 3 := by
  have hik : i ≠ k := by omega
  have hjk' : j ≠ k := by omega
  have hij' : i ≠ j := by omega
  simp [Finset.card_insert_of_not_mem, Finset.mem_insert,
        Finset.mem_singleton, hij', hik, hjk']

theorem pedigree_extend (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k)
    (S : Finset (Finset ℕ))
    (hS : Pedigree (k-1) S)
    (hedge : (j ≤ 3) ∨ (∃ t ∈ S, t.max = some j ∧ i ∈ t)) :
    Pedigree k (S ∪ {{i, j, k}}) := by
  unfold Pedigree isSolution isPreSolution
  have hnew : ({i, j, k} : Finset ℕ) ∉ S := by
    intro hmem
    -- All triangles in S have max ≤ k-1, but {i,j,k}.max = k
    have hmax := max_triple i j k hi hij hjk
    -- From isPreSolution: no triangle in S has max = some k (only up to k-1)
    have huniq := hS.1.1.2.2
    -- k ∉ Icc 3 (k-1), so no triangle in S should have max = k
    have : k ∉ Icc 3 (k-1) := by simp [Finset.mem_Icc]; omega
    -- But if {i,j,k} ∈ S then S has a triangle with max = k
    -- This contradicts that all max values in S are ≤ k-1
    -- (from isPreSolution: only layers 3,...,k-1 appear)
    sorry -- [not-mem]
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · -- card = k-2
    rw [Finset.card_union_of_disjoint (by simp [Finset.disjoint_left]; intro _ h; exact fun h' => hnew (h' ▸ h))]
    simp [Finset.card_singleton]
    have := hS.1.1.1; omega
  · -- ∀ t, t.card = 3
    intro t ht
    simp only [Finset.mem_union, Finset.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hS.1.1.2.1 t ht
    · exact card_triple i j k hij hjk
  · -- ∀ l ∈ Icc 3 k, ∃! t with t.max = some l
    intro l hl
    rw [Finset.mem_Icc] at hl
    by_cases hlk : l = k
    · subst hlk
      refine ⟨{i,j,k}, ?_, max_triple i j k hi hij hjk, ?_⟩
      · simp
      · intro t' ht' htmax'
        simp only [Finset.mem_union, Finset.mem_singleton] at ht'
        rcases ht' with ht' | rfl
        · -- t' ∈ S has max = some k, contradicts S = Pedigree(k-1)
          exfalso; sorry -- [max-k-in-S]
        · rfl
    · -- l ≤ k-1
      have hl' : l ∈ Icc 3 (k-1) := Finset.mem_Icc.mpr ⟨hl.1, by omega⟩
      obtain ⟨t, ht_mem, ht_max, ht_uniq⟩ := hS.1.1.2.2 l hl'
      refine ⟨t, Finset.mem_union_left _ ht_mem, ht_max, ?_⟩
      intro t' ht' htmax'
      simp only [Finset.mem_union, Finset.mem_singleton] at ht'
      rcases ht' with ht' | rfl
      · exact ht_uniq t' ht' htmax'
      · exfalso
        rw [max_triple i j k hi hij hjk] at htmax'
        exact absurd htmax' (by simp; omega)
  · -- Distinct pairs
    intro t1 ht1 t2 ht2 hcond
    simp only [Finset.mem_union, Finset.mem_singleton] at ht1 ht2
    rcases ht1 with ht1 | rfl <;> rcases ht2 with ht2 | rfl
    · -- both in S
      exact hS.1.2 t1 ht1 t2 ht2 hcond
    · -- t1 ∈ S, t2 = {i,j,k}
      intro heq
      sorry -- [distinct-new]
    · -- t1 = {i,j,k}, t2 ∈ S
      intro heq
      sorry -- [distinct-new-sym]
    · -- both {i,j,k}: k1=k2=k so k1 < k2 false
      intro heq
      simp [max_triple i j k hi hij hjk] at hcond
      omega
  · -- Generator condition
    intro t ht
    simp only [Finset.mem_union, Finset.mem_singleton] at ht
    rcases ht with ht | rfl
    · -- t ∈ S: use hS.2, but need to lift t_prev from S to S ∪ {new}
      have hgen := hS.2 t ht
      rcases hgen with hprim | ⟨t_prev, ht_prev, hmax, himem⟩
      · left; exact hprim
      · right; exact ⟨t_prev, Finset.mem_union_left _ ht_prev, hmax, himem⟩
    · -- t = {i,j,k}: need generator
      -- pair = {i,j,k}.erase k = {i,j}, b = j, a = i
      -- Need: {i,j} ⊆ {1,2,3} ∨ ∃ t_prev with max=j ∧ i ∈ t_prev
      simp only [max_triple i j k hi hij hjk, Option.getD_some]
      simp only [show ({i,j,k} : Finset ℕ).erase k = {i,j} from by
        ext x; simp [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega]
      simp only [show ({i,j} : Finset ℕ).max = some j from by
        simp [Finset.max_insert, Finset.max_singleton]; omega]
      simp only [show ({i,j} : Finset ℕ).min = some i from by
        simp [Finset.min_insert, Finset.min_singleton]; omega]
      simp only [Option.getD_some]
      rcases hedge with hj3 | ⟨t_prev, ht_prev, hmax, himem⟩
      · left
        intro x hx
        simp [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp <;> omega
      · right
        exact ⟨t_prev, Finset.mem_union_left _ ht_prev, hmax, himem⟩

end MembershipProject.Core
