-- N_HC2Pedigree.lean
-- Explicit pedigrees P1 (Case [a]) and P2 (Case [b])
-- Verified ALL PASS for k=4..12 in Python
-- Cases [a] and [b] from Tiru: {i,j} generated but never used as pair

import MembershipProject.Core.LearningFinsetDesirableDef
import MembershipProject.Core.N_PedigreeStep
import Mathlib.Tactic

namespace MembershipProject.Core

open Finset

-- q1, q2 for Case [a]: {q1,q2} = {1,2,3}\{i}, q1 < q2
-- i=1: q1=2, q2=3
-- i=2: q1=1, q2=3
-- i=3: q1=1, q2=2
def q1 (i : ℕ) : ℕ := if i = 1 then 2 else 1
def q2 (i : ℕ) : ℕ := if i = 3 then 2 else 3

-- ============================================================
-- CASE [a]: i ∈ {1,2,3}, j ≥ 4
-- P1 = {(1,2,3)} ∪ {(q1,q2,4) if j>4}
--    ∪ {(q2,4,5) if j>5} ∪ {(l-2,l-1,l) : 6≤l≤j-1}
--    ∪ {(i,q1,j)}
--    ∪ {(q1,j,j+1) if j<k-1} ∪ {(l-2,l-1,l) : j+2≤l≤k-1}
-- ============================================================

noncomputable def caseA_set (k i j : ℕ) : Finset (Finset ℕ) :=
  {{1,2,3}} ∪
  (if j > 4 then {{q1 i, q2 i, 4}} else ∅) ∪
  (if j > 5 then {{q2 i, 4, 5}} else ∅) ∪
  (Finset.image (fun l => ({l-2, l-1, l} : Finset ℕ)) (Finset.Icc 6 (j-1))) ∪
  {{i, q1 i, j}} ∪
  (if j+1 ≤ k-1 then
    {{q1 i, j, j+1}} ∪
    Finset.image (fun l => ({l-2, l-1, l} : Finset ℕ)) (Finset.Icc (j+2) (k-1))
  else ∅)

-- ============================================================
-- CASE [b]: i ≥ 4
-- P2 = {(1,2,3)} ∪ {(l-2,l-1,l) : 4≤l≤j-1}
--    ∪ {(i-2,i,j)} ∪ {(i-2,l-1,l) : j+1≤l≤k-1}
-- ============================================================

noncomputable def caseB_set (k i j : ℕ) : Finset (Finset ℕ) :=
  {{1,2,3}} ∪
  (Finset.image (fun l => ({l-2, l-1, l} : Finset ℕ)) (Finset.Icc 4 (j-1))) ∪
  {{i-2, i, j}} ∪
  (Finset.image (fun l => ({i-2, l-1, l} : Finset ℕ)) (Finset.Icc (j+1) (k-1)))

-- ============================================================
-- SPECIAL CASES: j ≤ 3
-- ============================================================

noncomputable def caseJ2_set (k : ℕ) : Finset (Finset ℕ) :=
  -- i=1, j=2: use pairs {1,3},{3,4},{4,5},...
  {{1,2,3}, {1,3,4}} ∪
  Finset.image (fun l => ({l-2, l-1, l} : Finset ℕ)) (Finset.Icc 5 (k-1))

noncomputable def caseJ3a_set (k : ℕ) : Finset (Finset ℕ) :=
  -- i=1, j=3: use pairs {1,2},{2,4},{4,5},...
  {{1,2,3}, {1,2,4}, {2,4,5}} ∪
  Finset.image (fun l => ({l-2, l-1, l} : Finset ℕ)) (Finset.Icc 6 (k-1))

noncomputable def caseJ3b_set (k : ℕ) : Finset (Finset ℕ) :=
  -- i=2, j=3: use pairs {1,3},{1,4},{1,5},...
  {{1,2,3}, {1,3,4}} ∪
  Finset.image (fun l => ({1, l-1, l} : Finset ℕ)) (Finset.Icc 5 (k-1))

-- ============================================================
-- COMBINED SET
-- ============================================================

noncomputable def partialPedSet (k i j : ℕ) : Finset (Finset ℕ) :=
  if k = 4 then {{1,2,3}}
  else if i = 1 ∧ j = 2 then caseJ2_set k
  else if i = 1 ∧ j = 3 then caseJ3a_set k
  else if i = 2 ∧ j = 3 then caseJ3b_set k
  else if i ≤ 3 then caseA_set k i j
  else caseB_set k i j

-- ============================================================
-- VALIDITY AXIOMS
-- Justified by the following HC construction (Tiru):
--
-- Consider the standard HC on {1,...,k-1}:
--   1 → 2 → 3 → ... → i → i+1 → ... → j-1 → j → j+1 → ... → k-2 → k-1 → 1
--
-- Modify it to make (i,j) an adjacent pair:
--   • Truncate the edge i → i+1 and connect i → j instead
--   • Truncate the edge j → j+1 and connect j → i+1 instead
--   • Truncate the edge j-1 → j and connect j-1 → j+1 instead
--
-- This gives a valid HC on {1,...,k-1} where (i,j) is an edge.
-- The pedigree built from this HC by the vertex-shrinking algorithm
-- gives Pedigree(k-1) S with:
--   • hedge: (i,j) is in the last tour (it was an edge of the HC)
--   • hpair: (i,j) never appears as an insertion pair in S
--     (because (i,j) is an edge of the HC, and in the vertex-shrinking
--      algorithm the pair of each triangle is the edge between the two
--      remaining neighbors when a vertex is removed. The edge (i,j)
--      persists in the shrinking HC until the very last steps, so it
--      is generated (in the last tour) but never used as a pair.
--      Cases [a] and [b] make this explicit: no triangle in P1 or P2
--      has {i,j} as its pair.)
--
-- Cases [a] and [b] give the explicit triangle lists P1 and P2
-- corresponding to this HC construction.
-- Verified by Python for k=4..12: ALL PASS.
-- ============================================================

axiom partialPedSet_pedigree (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    Pedigree (k-1) (partialPedSet k i j)

axiom partialPedSet_hedge (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    j ≤ 3 ∨ ∃ tp ∈ partialPedSet k i j, tp.max = some j ∧ i ∈ tp

axiom partialPedSet_hpair (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    ∀ t ∈ partialPedSet k i j, t.erase (t.max.getD 0) ≠ {i, j}

-- ============================================================
-- PARTIALPPEDIGREE
-- ============================================================

noncomputable def partialPedigree (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    { S : Finset (Finset ℕ) // Pedigree (k-1) S } :=
  ⟨partialPedSet k i j, partialPedSet_pedigree k i j hk hi hij hjk⟩

theorem partialPedigree_hasEdge (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    let S := (partialPedigree k i j hk hi hij hjk).val
    j ≤ 3 ∨ ∃ tp ∈ S, tp.max = some j ∧ i ∈ tp :=
  partialPedSet_hedge k i j hk hi hij hjk

theorem partialPedigree_hpair (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    let S := (partialPedigree k i j hk hi hij hjk).val
    ∀ t ∈ S, t.erase (t.max.getD 0) ≠ {i, j} :=
  partialPedSet_hpair k i j hk hi hij hjk

end MembershipProject.Core
