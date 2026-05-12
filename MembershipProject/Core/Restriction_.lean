-- Core/RestrictionFull.lean
-- ========================================================
-- Restricted Network Construction
-- Paper: "A Strongly Polynomial Algorithm for Membership
--        in the Pedigree Polytope" by Tiru Arthanari
-- Section 4.3.1: Definition 8 (Restricted Network N_{k-1}(L))
-- ========================================================

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import MembershipProject.Core.Basic
import MembershipProject.Core.Types

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace MembershipProject.Core

open Nat

-- ============================================
-- TRIPLE REPRESENTATION (wrapper for Node)
-- ============================================

/-- A triple (i,j,k) with constraints i < j < k -/
structure Triple where
  i : ℕ
  j : ℕ
  k : ℕ
  h_ij : i < j
  h_jk : j < k
  deriving DecidableEq, Repr

/-- A triple with vertex bounds 1 ≤ i < j < k ≤ n -/
structure BoundedTriple (n : ℕ) extends Triple where
  h_1i : 1 ≤ i
  h_kn : k ≤ n

/-- Convert Triple to Node -/
def Triple.toNode (t : Triple) : Node := ⟨t.i, t.j, t.k⟩

/-- Convert Node to Triple (requires proofs of constraints) -/
def Node.toTriple (nd : Node) (h_ij : nd.i < nd.j) (h_jk : nd.j < nd.k) : Triple :=
  { i := nd.i, j := nd.j, k := nd.k, h_ij := h_ij, h_jk := h_jk }

/-- Node capacities: mapping from triples to rational values -/
structure NodeCapacities where
  caps : Triple → Rat
  nonneg : ∀ t : Triple, caps t ≥ 0

-- ============================================
-- LAYER NOTATION
-- ============================================

/-- Δ^k denotes all nodes (triples) at layer k -/
def Delta (k : ℕ) : Finset Triple :=
  if h : k ≥ 3 then
    ((Finset.Ico 1 k).attach.biUnion fun ⟨i, hi⟩ =>
      have hi_bound : i < k := (Finset.mem_Ico.1 hi).right
      ((Finset.Ico (i+1) k).attach.image fun ⟨j, hj⟩ =>
        have h_i_lt_j : i < j := by
          have : i + 1 ≤ j := (Finset.mem_Ico.1 hj).left; omega
        have h_j_lt_k : j < k := (Finset.mem_Ico.1 hj).right
        Triple.mk i j k h_i_lt_j h_j_lt_k))
  else ∅

def allTriplesWithK := Delta

-- ============================================
-- GENERATOR SETS
-- ============================================

/-- G(u) = generators of node u = {i, j, k}
    Section 4.3.1: Definition of generators for deletion rules -/
def generators (u : Triple) : Finset Triple :=
  if u.i = 1 ∧ u.j = 2 ∧ u.k = 3 then
    ∅
  else if u.j > 3 then
    let i := u.i
    let j := u.j
    let form1 := (Finset.Ico 1 i).attach.biUnion fun ⟨r, hr⟩ =>
      have h_r_lt_i : r < i := (Finset.mem_Ico.1 hr).right
      (if h : i < j then
        some (Triple.mk r i j h_r_lt_i h)
      else none).toFinset
    let form2 := (Finset.Ico (i+1) j).attach.biUnion fun ⟨s, hs⟩ =>
      have h_i_lt_s : i < s := by
        have := (Finset.mem_Ico.1 hs).left; omega
      have h_s_lt_j : s < j := (Finset.mem_Ico.1 hs).right
      (if h : i < j then
        some (Triple.mk i s j h_i_lt_s h_s_lt_j)
      else none).toFinset
    form1 ∪ form2
  else
    {Triple.mk 1 2 3 (by omega) (by omega)}

-- [Additional lemmas and deletion rules A-G follow...]
-- ============================================================================
-- ADD THESE TWO LEMMAS TO Core/RestrictionFull.lean
-- Place them immediately after the `generators` definition
-- (before the LINK REPRESENTATION section)
-- ============================================================================

/-- A generator u of t (when t.j > 3) lives at layer t.j.

    That is: if u ∈ generators(t) and t.j > 3 then u.k = t.j.
    This formalises the book's key property: G(v = {i,j,k}) depends only
    on the common edge {i,j}, not on the layer k. -/
lemma mem_generators_layer {t u : Triple}
    (ht : ¬(t.i = 1 ∧ t.j = 2 ∧ t.k = 3))
    (hj : t.j > 3)
    (hmem : u ∈ generators t) : u.k = t.j := by
  simp only [generators, if_neg ht, if_pos hj,
             Finset.mem_union, Finset.mem_biUnion, Finset.mem_attach,
             Finset.mem_Ico, dif_pos t.h_ij,
             Option.toFinset_some, Finset.mem_singleton, true_and] at hmem
  -- form1: u = Triple.mk r t.i t.j ...   → u.k = t.j ✓
  -- form2: u = Triple.mk t.i s t.j ...   → u.k = t.j ✓
  obtain ⟨⟨r, _⟩, _, rfl⟩ | ⟨⟨s, _⟩, _, rfl⟩ := hmem <;> rfl

/-- A generator u of t (when t.j > 3) satisfies: u.i = t.i (form2) or u.j = t.i (form1).

    This formalises: generators of {i,j,k} with j > 3 are
      form1: {r, i, j} with r < i  →  u.j = t.i
      form2: {i, s, j} with i < s < j  →  u.i = t.i
    So in either case the common edge {i,j} of t appears in u. -/
lemma mem_generators_common_edge {t u : Triple}
    (ht : ¬(t.i = 1 ∧ t.j = 2 ∧ t.k = 3))
    (hj : t.j > 3)
    (hmem : u ∈ generators t) : u.i = t.i ∨ u.j = t.i := by
  simp only [generators, if_neg ht, if_pos hj,
             Finset.mem_union, Finset.mem_biUnion, Finset.mem_attach,
             Finset.mem_Ico, dif_pos t.h_ij,
             Option.toFinset_some, Finset.mem_singleton, true_and] at hmem
  obtain ⟨⟨r, _⟩, _, rfl⟩ | ⟨⟨s, _⟩, _, rfl⟩ := hmem
  · right; rfl   -- form1: (Triple.mk r t.i t.j ...).j = t.i ✓
  · left;  rfl   -- form2: (Triple.mk t.i s t.j ...).i = t.i ✓
/-- Every triple in Δ_k has i ≥ 1.
    The outer iterator of Delta is Finset.Ico 1 k, so the i-component
    of any member satisfies 1 ≤ i by construction.
    Used in Pedigree.toCompact to close h_lower_bound (Option B). -/
lemma mem_delta_i_pos {k : ℕ} {t : Triple} (hmem : t ∈ Delta k) : 1 ≤ t.i := by
  unfold Delta at hmem
  split_ifs at hmem with hk
  · -- hk : k ≥ 3; hmem is membership in the biUnion/image
    rw [Finset.mem_biUnion] at hmem
    obtain ⟨⟨i, hi_mem⟩, _, hmem'⟩ := hmem
    -- hi_mem : i ∈ Finset.Ico 1 k  →  1 ≤ i
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi_mem).1
    -- hmem' : t ∈ (Finset.Ico (i+1) k).attach.image (fun ⟨j,_⟩ => Triple.mk i j k ...)
    rw [Finset.mem_image] at hmem'
    obtain ⟨_, _, rfl⟩ := hmem'
    -- after rfl: t = Triple.mk i _ k _ _  so t.i = i
    exact hi1
  · exact absurd hmem (Finset.notMem_empty _)
structure Link  where
  u : Triple
  v : Triple
  h_consecutive : u.k + 1 = v.k
  deriving Repr

-- ============================================
-- DELETION RULES FOR RESTRICTED NETWORK
-- ============================================

namespace Restriction

/-- Rule (a): Include {i, j, l} in D for l ∈ [max(4, j), k-1]

    For link L = (u=(r,s,k), v=(i,j,k+1)), delete all nodes with edge (i,j)
    at layers from max(4,j) up to k-1 -/
def ruleA (link : Link) : Finset Triple :=
  let i := link.v.i
  let j := link.v.j
  let k := link.u.k
  let start := max 4 j
  (Finset.Ico start k).attach.biUnion fun ⟨l, hl⟩ =>
    have ⟨_, h_l_lt_k⟩ := Finset.mem_Ico.1 hl
    (if h : i < j ∧ j < l then
      some (Triple.mk i j l h.1 h.2)
    else none).toFinset

def ruleB  (link : Link ) : Finset (Triple) :=
  let r := link.u.i
  let s := link.u.j
  let k := link.u.k
  let start := max 4 s
  (Finset.Ico start k).attach.biUnion fun ⟨l, hl⟩ =>
    have ⟨_, h_l_lt_k⟩ := Finset.mem_Ico.1 hl
    (if h : r < s ∧ s < l then
      some (Triple.mk r s l h.1 h.2)
    else none).toFinset

def ruleC (link : Link) : Finset Triple :=
  (Delta link.u.j).filter fun w => w ∉ generators link.u

def ruleD (link : Link) : Finset Triple :=
  (Delta link.v.j).filter fun w => w ∉ generators link.v

def ruleE (link : Link) : Finset Triple :=
  (Delta link.u.k).filter fun w => w ≠ link.u

def ruleFStep (D : Finset Triple) (allNodes : Finset Triple) : Finset Triple :=
  allNodes.filter fun node =>
    node.k > 4 ∧
    node ∉ D ∧
    (generators node).Nonempty ∧
    (generators node) ⊆ D

def ruleF (link : Link) (D_initial : Finset Triple)
    (fuel : ℕ) : Finset Triple :=
  let k := link.u.k
  let allNodes := (Finset.range (k + 1)).biUnion fun l => Delta l
  match fuel with
  | 0 => ∅
  | fuel' + 1 =>
    let newDeleted := ruleFStep D_initial allNodes
    if newDeleted.Nonempty then
      ruleF link (D_initial ∪ newDeleted) fuel'
    else
      ∅

structure RigidPedigree where
  nodes : List Triple
  flow : Rat
  deriving Repr

def ruleG (link : Link) (D : Finset Triple)
    (rigidPedigrees : List RigidPedigree) : Finset Triple :=
  let affectedPedigrees := rigidPedigrees.filter fun P =>
    P.nodes.any fun node => node ∈ D
  affectedPedigrees.foldl (fun acc P =>
    acc ∪ P.nodes.toFinset) ∅

def computeDComplete (link : Link)
    (rigidPedigrees : List RigidPedigree)
    (fuel : ℕ := 100) : Finset Triple :=
  let D_basic :=
    ruleA link ∪ ruleB link ∪ ruleC link ∪ ruleD link ∪ ruleE link
  let D_with_f := D_basic ∪ ruleF link D_basic fuel
  let D_final := D_with_f ∪ ruleG link D_with_f rigidPedigrees
  D_final

def computeD_legacy (t1 t2 : Triple) : Finset (Triple) :=
  if h : t1.k + 1 = t2.k then
    let link : Link := { u := t1, v := t2, h_consecutive := h }
    ruleA link ∪ ruleB link ∪ ruleC link ∪ ruleD link ∪ ruleE link
  else
    ∅

def computeD (t1 t2 : Triple) : Finset Triple :=
  computeD_legacy t1 t2

def restrictCapacities (caps : NodeCapacities) (D : Finset Triple) : NodeCapacities where
  caps t := if t ∈ D then 0 else caps.caps t
  nonneg t := by
    by_cases h : t ∈ D
    · simp only [h, ↓reduceIte]; norm_num
    · simp only [h, ↓reduceIte]; exact caps.nonneg t

def restrictedVertexSet (k : ℕ) (D : Finset Triple) : Finset Triple :=
  (Finset.range k).biUnion (fun l => Delta l) |>.filter fun t => t ∉ D
end Restriction

end MembershipProject.Core

-- ============================================
-- EXAMPLES AND TESTS
-- ============================================

section GeneratorExamples

open MembershipProject.Core

-- Example 1: G({2, 4, 6}) = {{1, 2, 4}, {2, 3, 4}}
example :
  let v := Triple.mk 2 4 6 (by omega) (by omega)
  let expected := {
    Triple.mk 1 2 4 (by omega) (by omega),
    Triple.mk 2 3 4 (by omega) (by omega)
  }
  generators v = expected := by native_decide

-- Example 2: G({2, 3, 7}) = {{1, 2, 3}}
example :
  let v := Triple.mk 2 3 7 (by omega) (by omega)
  let expected := {Triple.mk 1 2 3 (by omega) (by omega)}
  generators v = expected := by native_decide

-- Example 3: G({2, 4, 6}) = G({2, 4, 8})
example :
  let v1 := Triple.mk 2 4 6 (by omega) (by omega)
  let v2 := Triple.mk 2 4 8 (by omega) (by omega)
  generators v1 = generators v2 := by native_decide

-- Example 4: G({1, 2, 3}) = ∅
example :
  let root := Triple.mk 1 2 3 (by omega) (by omega)
  generators root = ∅ := by native_decide

-- Example 5: G({1, 3, 5}) = {{1, 2, 3}}
example :
  let v := Triple.mk 1 3 5 (by omega) (by omega)
  let expected := {Triple.mk 1 2 3 (by omega) (by omega)}
  generators v = expected := by native_decide

-- Example 6: G({3, 5, 7}) = {{1,3,5}, {2,3,5}, {3,4,5}}
example :
  let v := Triple.mk 3 5 7 (by omega) (by omega)
  let expected : Finset Triple := {
    Triple.mk 1 3 5 (by omega) (by omega),
    Triple.mk 2 3 5 (by omega) (by omega),
    Triple.mk 3 4 5 (by omega) (by omega)
  }
  generators v = expected := by native_decide
end GeneratorExamples
