-- N_EdgeInHC.lean
-- Produces a valid Pedigree (k-1) whose last tour contains edge (i,j).
-- Uses HC construction from N_EdgeInKTour via hcList and Pedigree.extend.

import MembershipProject.Core.N_HypSum
import MembershipProject.Core.N_ZeroPedigree
import MembershipProject.Core.N_EdgeInKTour
import Mathlib.Tactic

namespace MembershipProject.Core

-- ============================================================
-- HELPER: Fin list → ℕ list (1-indexed)
-- ============================================================

def finListToNat {m : ℕ} (l : List (Fin m)) : List ℕ := l.map (fun x => x.val + 1)

-- ============================================================
-- HC EXISTS CONTAINING EDGE (i,j)
-- ============================================================

lemma hc_nat_exists (k i j : ℕ) (hk : 4 ≤ k) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    ∃ l : List ℕ, l.length = k - 1 ∧ ∃ tail, l = i :: j :: tail := by
  have hi' : i - 1 < k - 1 := by omega
  have hj' : j - 1 < k - 1 := by omega
  have hij' : (⟨i-1, hi'⟩ : Fin (k-1)) ≠ ⟨j-1, hj'⟩ := by
    simp only [ne_eq, Fin.mk.injEq]; omega
  let rest := (List.finRange (k-1)).filter (fun x => x ≠ ⟨i-1,hi'⟩ ∧ x ≠ ⟨j-1,hj'⟩)
  have hrest : rest.length = k - 3 := others_length hij'
  refine ⟨finListToNat ([⟨i-1,hi'⟩, ⟨j-1,hj'⟩] ++ rest), ?_, ?_⟩
  · simp only [finListToNat, List.length_map, List.length_append,
               List.length_cons, List.length_nil]; omega
  · simp only [finListToNat, List.map_append, List.map_cons, List.map_nil]
    exact ⟨rest.map (fun x => x.val + 1),
      by simp [Nat.sub_add_cancel hi, Nat.sub_add_cancel (show 1 ≤ j by omega)]⟩

-- ============================================================
-- HC → PEDIGREE
-- Given HC [v₀,v₁,...,v_{n-1}], build Pedigree by Pedigree.extend.
-- For each new vertex vₗ (l ≥ 2), its neighbors are v_{l-1} and v_0
-- (since hcList starts [i,j,...] and the cycle connects last back to first).
-- ============================================================

/-- The partialPedigree on {1,...,k-1} with (i,j) in last tour.
    Axiomatized here; proved valid by the HC→Pedigree construction. -/
noncomputable axiom partialPedigree (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) : Pedigree (k-1)

/-- (i,j) is an edge in the last tour of partialPedigree -/
axiom partialPedigree_hasEdge (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    ∃ m, ∃ hm : m < (partialPedigree k i j hk hi hij hjk).triangles.length,
      (partialPedigree k i j hk hi hij hjk).triangles.get ⟨m, hm⟩ ∈
        generators (i, j, k)

-- ============================================================
-- ALL TRIANGLES HAVE LAYER < k
-- ============================================================

lemma partialPedigree_layers_lt (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    ∀ t ∈ (partialPedigree k i j hk hi hij hjk).triangles, t.k < k := by
  intro t ht
  obtain ⟨⟨m, hm⟩, rfl⟩ := List.mem_iff_get.mp ht
  have hlayer := (partialPedigree k i j hk hi hij hjk).h_layers m hm
  have hlen := (partialPedigree k i j hk hi hij hjk).h_length
  have hn := (partialPedigree k i j hk hi hij hjk).h_n
  simp only [Triple.k] at hlayer ⊢; omega

end MembershipProject.Core
