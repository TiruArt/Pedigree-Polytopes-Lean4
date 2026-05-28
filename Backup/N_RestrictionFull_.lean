-- File No. 3 - N_RestrictionFull.lean
-- Generators G(e) for a triple e, and the RigidEntry type.
--
-- G(e) is the set of triples that can precede e in a pedigree:
-- the triples (r,s,l) such that edge (r,s) was in the tour
-- just before edge (i,j) = (e.i, e.j) was available for insertion.
--
-- Reference: Arthanari, T.S. Pedigree Polytopes, Springer Nature, 2023.
--            Chapter 3 (Multistage Insertion).
-- Preprint:  Arthanari, T.S. "On the Importance of Studying the
--            Membership Problem for Pedigree Polytopes."
--            arXiv:2507.09069v1 [math.CO].

import MembershipProject.Core.N_Basic

namespace MembershipProject.Core

open Nat

-- ============================================================
-- GENERATORS
-- G(t) = generators t = the set of triples that generate edge (t.i, t.j).
--
-- A triple e' = (r, s, l) is a generator of t = (i, j, k) if
-- edge (r, s) was present in the tour at the stage when (i, j)
-- first became available for insertion (i.e. at layer j).
--
-- Three cases:
--   t = (1,2,3): G(t) = ∅
--     The base triple has no generator — it is the initial 3-tour.
--
--   t.j > 3: G(t) = form1 ∪ form2 where
--     form1 = { (r, t.i, t.j) | 1 ≤ r < t.i }  (edges ending at t.i)
--     form2 = { (t.i, s, t.j) | t.i < s < t.j } (edges starting at t.i)
--     These are all edges incident to t.i in the (t.j)-tour.
--
--   t.j ≤ 3, t ≠ (1,2,3): G(t) = { (1,2,3) }
--     The edge (t.i, t.j) is in E_3 (the initial 3-tour),
--     so its only generator is the base triple (1,2,3).
--
-- Key property: G(t) depends only on (t.i, t.j), not on t.k,
-- for t.k > 3. (Proved below as generators_ij_only.)
-- ============================================================

def generators (t : Triple) : Finset Triple :=
  if t.i = 1 ∧ t.j = 2 ∧ t.k = 3 then
    ∅
  else if t.j > 3 then
    (Finset.Ico 1 t.i).image         (fun r => (r,   t.i, t.j)) ∪
    (Finset.Ico (t.i + 1) t.j).image (fun s => (t.i, s,   t.j))
  else
    {(1, 2, 3)}

-- G(t) depends only on (t.i, t.j) when t.k > 3.
-- This means generators can be computed from the edge alone,
-- independent of the layer at which it appears.
lemma generators_ij_only {i j k1 k2 : ℕ} (hk1 : k1 > 3) (hk2 : k2 > 3) :
    generators (i, j, k1) = generators (i, j, k2) := by
  simp [generators, show ¬(i = 1 ∧ j = 2 ∧ k1 = 3) from by omega,
                    show ¬(i = 1 ∧ j = 2 ∧ k2 = 3) from by omega]

-- Every generator of t lies in Delta t.j (when t.j > 3)
-- or in Delta 3 (when t.j ≤ 3).
-- This confirms generators are valid triples at the correct layer.
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

-- G(t) ⊆ Delta t.j when t.j > 3.
lemma generators_subset_Delta {t : Triple} (ht_i : 1 ≤ t.i) (ht_ij : t.i < t.j)
    (htj : t.j > 3) : generators t ⊆ Delta t.j := by
  intro e' he'
  have h := mem_generators_Delta ht_i ht_ij he'
  rwa [if_pos htj] at h

-- ============================================================
-- RIGID PEDIGREE ENTRY
-- A RigidEntry n bundles a pedigree with its fixed weight μ_P.
-- Rigid pedigrees appear in every convex combination expressing
-- X/k as a convex combination of pedigrees in P_k.
-- Defined in N_PedigreeDefinition.lean (after the Pedigree structure).
-- Used in: N_RestrictionAll.lean (R_k^1, R_k^2, R_k).
-- ============================================================

end MembershipProject.Core
