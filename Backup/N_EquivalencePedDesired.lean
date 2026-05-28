-- N_EquivalencePedDesired.lean
-- Pedigree → isDesiredSolution

import MembershipProject.Core.N_HypSum
import MembershipProject.Core.LearningFinsetDesirableDef
import Mathlib.Tactic

namespace MembershipProject.Core

open Finset

def tripleToFinset (t : Triple) : Finset ℕ := {t.1, t.2.1, t.2.2}

def triplesToFinsetFinset (ts : List Triple) : Finset (Finset ℕ) :=
  (ts.map tripleToFinset).toFinset

-- Helper: triangles at different positions have different layers
lemma triangles_nodup (n : ℕ) (P : Pedigree n) :
    (P.triangles.map tripleToFinset).Nodup := by
  apply List.Nodup.map
  · -- tripleToFinset injective: different max → different finset
    intro ⟨a1, b1, k1⟩ ⟨a2, b2, k2⟩ heq
    simp [tripleToFinset] at heq
    -- {a1,b1,k1} = {a2,b2,k2} implies k1 = k2 (both are max)
    -- then a1=a2, b1=b2 follows
    sorry -- [inj]
  · -- triangles list nodup: distinct layers from h_layers
    rw [List.nodup_iff_injOn_get]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    -- triangles[i] = triangles[j] implies i = j via h_layers
    have hki := P.h_layers i hi
    have hkj := P.h_layers j hj
    simp [Triple.k] at heq hki hkj
    ext; simp; omega

theorem Pedigree_isDesiredSolution (n : ℕ) (P : Pedigree n) :
    isDesiredSolution n (triplesToFinsetFinset P.triangles) := by
  unfold isDesiredSolution isSolution isPreSolution triplesToFinsetFinset
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩

  · -- S.card = n-2
    rw [List.toFinset_card_of_nodup (triangles_nodup n P),
        List.length_map, P.h_length]

  · -- ∀ t ∈ S, t.card = 3
    intro t ht
    simp only [List.mem_toFinset, List.mem_map] at ht
    obtain ⟨⟨a, b, k⟩, hmem, rfl⟩ := ht
    -- Get h_in_delta for this triangle
    obtain ⟨⟨pos, hpos⟩, hget⟩ := List.mem_iff_get.mp hmem
    have hdelta := P.h_in_delta pos hpos
    rw [mem_Delta_iff] at hdelta
    obtain ⟨ha, hab, hbk⟩ := hdelta
    -- {a, b, k}.card = 3 since 1 ≤ a < b < k
    simp only [tripleToFinset, Triple.i, Triple.j, Triple.k]
    have hak : a ≠ k := by omega
    have hbk' : b ≠ k := by omega
    have hab' : a ≠ b := by omega
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_singleton]
    · simp [hbk']
    · simp [hab', hak]

  · -- ∀ k ∈ Icc 3 n, ∃! t with t.max = some k
    intro k hk
    rw [Finset.mem_Icc] at hk
    -- Triangle at position k-3 has max k
    have hpos : k - 3 < P.triangles.length := by
      rw [P.h_length]; omega
    let triple := P.triangles.get ⟨k-3, hpos⟩
    have hlayer := P.h_layers (k-3) hpos
    have hdelta := P.h_in_delta (k-3) hpos
    rw [mem_Delta_iff] at hdelta
    obtain ⟨ha, hab, hbk⟩ := hdelta
    -- triple has max = k
    have hmax : (tripleToFinset triple).max = some k := by
      simp [tripleToFinset, Triple.i, Triple.j, Triple.k, triple]
      rw [show triple.k = k-3+3 from hlayer]
      simp [Finset.max_insert]
      constructor
      · omega
      · constructor <;> omega
    refine ⟨tripleToFinset triple, ?_, hmax, ?_⟩
    · simp [List.mem_toFinset, List.mem_map]
      exact ⟨triple, List.get_mem _ _ _, rfl⟩
    · -- Uniqueness: only one triangle per layer
      intro t' ht' hmax'
      simp [List.mem_toFinset, List.mem_map] at ht'
      obtain ⟨⟨a', b', k'⟩, hmem', rfl⟩ := ht'
      obtain ⟨⟨pos', hpos'⟩, hget'⟩ := List.mem_iff_get.mp hmem'
      have hlayer' := P.h_layers pos' hpos'
      -- max of {a',b',k'} = k means k' = k
      have hk'k : k' = k := by
        simp [tripleToFinset, Triple.k] at hmax'
        sorry -- [max-eq] k' = k from max condition
      -- Then pos' = k-3 = pos by h_layers
      have hpos_eq : pos' = k - 3 := by
        have := P.h_layers pos' hpos'
        simp [Triple.k] at this; omega
      simp [tripleToFinset]
      congr 1
      · sorry -- a' = a
      · sorry -- b' = b
      · exact hk'k

  · -- Distinct pairs: from h_distinct
    intro t1 ht1 t2 ht2 hcond
    simp [List.mem_toFinset, List.mem_map] at ht1 ht2
    obtain ⟨⟨a1,b1,k1⟩, hmem1, rfl⟩ := ht1
    obtain ⟨⟨a2,b2,k2⟩, hmem2, rfl⟩ := ht2
    obtain ⟨⟨p1,hp1⟩, hg1⟩ := List.mem_iff_get.mp hmem1
    obtain ⟨⟨p2,hp2⟩, hg2⟩ := List.mem_iff_get.mp hmem2
    intro heq
    -- erase max gives the pair, if pairs equal and k1 < k2 contradiction h_distinct
    sorry -- [distinct]

  · -- Generator condition: from h_generators
    intro t ht
    simp [List.mem_toFinset, List.mem_map] at ht
    obtain ⟨⟨a, b, k⟩, hmem, rfl⟩ := ht
    obtain ⟨⟨pos, hpos⟩, hget⟩ := List.mem_iff_get.mp hmem
    simp only [tripleToFinset, Triple.i, Triple.j, Triple.k]
    -- If pos = 0: triangle is (1,2,3), pair = {1,2} ⊆ {1,2,3} → primitive
    by_cases hpos0 : pos = 0
    · left
      have hfirst := P.h_first
      rw [List.head?_eq_get] at hfirst
      simp at hfirst
      rw [hpos0] at hget
      rw [← hget]
      simp [tripleToFinset]
      sorry -- [primitive] (1,2,3).erase 3 = {1,2} ⊆ {1,2,3}
    · -- pos > 0: use h_generators
      right
      have hgen := P.h_generators pos (by omega) hpos
      obtain ⟨j, hj, hj_gen⟩ := hgen
      -- hj_gen : triangles[j] ∈ generators triangles[pos]
      sorry -- [generator] convert to finset form

end MembershipProject.Core
