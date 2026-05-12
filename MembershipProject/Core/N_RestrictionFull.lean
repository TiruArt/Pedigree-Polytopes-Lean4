-- Core/N_RestrictionFull.lean
-- Generators and rigid pedigrees. Triple = ℕ × ℕ × ℕ.

import MembershipProject.Core.N_Basic

namespace MembershipProject.Core

open Nat

-- ============================================================
-- GENERATORS
-- generators t = the set of triples that create edge (t.i, t.j)
-- at the stage when t.j is first inserted.
--
-- Rule:
--   t = (1,2,3)  →  ∅                        [initial triple]
--   t.j > 3      →  form1 ∪ form2 where
--                     form1 = {(r, t.i, t.j) | 1 ≤ r < t.i}
--                     form2 = {(t.i, s, t.j) | t.i < s < t.j}
--   else (t.j ≤ 3, t ≠ (1,2,3))  →  {(1, 2, 3)}
--
-- Key: generators depends only on (t.i, t.j), not t.k, for t.k > 3.
-- ============================================================

def generators (t : Triple) : Finset Triple :=
  if t.i = 1 ∧ t.j = 2 ∧ t.k = 3 then
    ∅
  else if t.j > 3 then
    (Finset.Ico 1 t.i).image         (fun r => (r,   t.i, t.j)) ∪
    (Finset.Ico (t.i + 1) t.j).image (fun s => (t.i, s,   t.j))
  else
    {(1, 2, 3)}

-- generators depends only on (t.i, t.j) when t.k > 3
lemma generators_ij_only {i j k1 k2 : ℕ} (hk1 : k1 > 3) (hk2 : k2 > 3) :
    generators (i, j, k1) = generators (i, j, k2) := by
  simp [generators, show ¬(i = 1 ∧ j = 2 ∧ k1 = 3) from by omega,
                    show ¬(i = 1 ∧ j = 2 ∧ k2 = 3) from by omega]

-- Every generator of t is in Delta t.j (t.j > 3) or Delta 3 (t.j ≤ 3)
lemma mem_generators_Delta {t e' : Triple} (ht_i : 1 ≤ t.i) (ht_ij : t.i < t.j)
    (he' : e' ∈ generators t) : e' ∈ Delta (if t.j > 3 then t.j else 3) := by
  simp only [generators] at he'
  split_ifs at he' with h1 h2
  · simp at he'
  · rw [if_pos h2]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Ico] at he'
    rcases he' with ⟨r, ⟨hr1, hr2⟩, rfl⟩ | ⟨s, ⟨hs1, hs2⟩, rfl⟩
    · exact mem_Delta_self r t.i hr1 (by omega) ht_ij
    · exact mem_Delta_self t.i s ht_i (by omega) (by omega)
  · rw [if_neg h2]
    simp only [Finset.mem_singleton] at he'
    subst he'
    exact mem_Delta_self 1 2 (by omega) (by omega) (by omega)

-- generators t ⊆ Delta t.j when t.j > 3
lemma generators_subset_Delta {t : Triple} (ht_i : 1 ≤ t.i) (ht_ij : t.i < t.j)
    (htj : t.j > 3) : generators t ⊆ Delta t.j := by
  intro e' he'
  have h := mem_generators_Delta ht_i ht_ij he'
  rwa [if_pos htj] at h

-- ============================================================
-- RIGID PEDIGREE ENTRY
-- RigidEntry is defined in N_PedigreeDefinition.lean (after Pedigree)
-- ============================================================

end MembershipProject.Core
