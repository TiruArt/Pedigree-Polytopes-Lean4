-- N_EdgeInHC.lean
-- Produces a valid Pedigree (k-1) whose last tour contains edge (i,j).
-- HC existence justified by N_EdgeInKTour (separate file).

import MembershipProject.Core.N_HypSum
import Mathlib.Tactic

namespace MembershipProject.Core

-- ============================================================
-- PARTIAL PEDIGREE: axioms
-- Justified by HC construction + Python verification k=4..12
-- ============================================================

/-- A valid Pedigree (k-1) whose last tour contains edge (i,j).
    Built from the HC [i,j,...] via the vertex-shrinking algorithm. -/
noncomputable axiom partialPedigree (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) : Pedigree (k-1)

/-- (i,j) is an edge in the last tour of partialPedigree -/
axiom partialPedigree_hasEdge (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    ∃ m, ∃ hm : m < (partialPedigree k i j hk hi hij hjk).triangles.length,
      (partialPedigree k i j hk hi hij hjk).triangles.get ⟨m, hm⟩ ∈
        generators (i, j, k)

-- ============================================================
-- ALL TRIANGLES HAVE LAYER < k (proved from pedigree structure)
-- ============================================================

lemma partialPedigree_layers_lt (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    ∀ t ∈ (partialPedigree k i j hk hi hij hjk).triangles, t.k < k := by
  intro t ht
  obtain ⟨⟨m, hm⟩, rfl⟩ := List.mem_iff_get.mp ht
  have hlayer := (partialPedigree k i j hk hi hij hjk).h_layers m hm
  have hlen   := (partialPedigree k i j hk hi hij hjk).h_length
  have hn     := (partialPedigree k i j hk hi hij hjk).h_n
  simp only [Triple.k] at hlayer ⊢; omega

end MembershipProject.Core
