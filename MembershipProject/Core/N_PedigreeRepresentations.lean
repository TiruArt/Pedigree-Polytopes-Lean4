-- Core/N_PedigreeRepresentations.lean
--
-- Pedagogical file: Four equivalent representations of a Pedigree.
--
-- This file documents the four ways a pedigree for n cities appears
-- in this Lean 4 formalization, explaining WHY each representation
-- is used and HOW they relate to each other and to the book.
--
-- Reference: Arthanari, T.S. Pedigree Polytopes, Springer Nature 2023.
--   Chapter 1: Pedigree as rooted tree in D+(Δ,A)
--   Chapter 4: Pedigree as sequence of common edges (List (Edge n))
--   Chapter 5: Pedigree as characteristic vector (Pedigree n struct)
--   Chapter 7: Pedigree as element of Finset
--   Chapter 3: Pedigree as MIR 0-1 solution (characteristic vector)
--
-- ======================================================================
-- THE FOUR REPRESENTATIONS
-- ======================================================================
--
-- REPRESENTATION 1: Pedigree n (struct) — N_PedigreeDefinition.lean
--
--   structure Pedigree (n : ℕ) where
--     triangles : List Triple   -- sequence of triangles
--     h_length  : triangles.length = n - 2
--     h_distinct: ∀ i j, i ≠ j → triangles[i].edge ≠ triangles[j].edge
--     h_generator: ∀ t ∈ triangles, hasGenerator t triangles
--
--   WHY: Natural for theorem proving. hypSum C P sums C(t) over non-default
--   triangles. Used in: N_ZeroPedigree, N_FullDimensional, N_Sufficiency.
--
-- REPRESENTATION 2: List (Edge n) — PedigreeBijection.lean
--
--   A pedigree is equivalently a sequence of n-3 common edges
--   (e_4, e_5, ..., e_n) where e_k = {i_k, j_k} ∈ E_{k-1}.
--   The bijection: pedigreeToEdges : Pedigree n → List (Edge n)
--
--   WHY: Natural for adjacency proofs. The swap operation works
--   directly on edge sequences. Used in: N_RigidAdjCase2a/b/c,
--   N_RigidAdjacency, SwappableImpliesNonAdjacent.
--
-- REPRESENTATION 3: Rooted tree in D+(Δ,A) — THIS FILE
--
--   D+(Δ,A) is the directed graph where:
--   - Δ = all triangles {i,j,k} for 1≤i<j<k≤n (nodes)
--   - A = arcs (u,v) if u is a generator of v
--   A pedigree = a rooted tree in D+(Δ,A) rooted at {1,2,3}
--   containing exactly one node per layer k=3,...,n.
--
--   WHY: This is the Chapter 1 definition. It makes the recursive
--   insertion structure explicit and is natural for algorithmic
--   implementation (see decideTree, decideIsParent below).
--   Used in: TreeDef.lean, TreeDefRandomTest.lean.
--
-- REPRESENTATION 4: Finset n — N_YisinConv.lean
--
--   A pedigree can be viewed as a subset S ⊆ Δ with |S| = n-2,
--   one triangle per layer. Natural for counting and set operations.
--
--   WHY: Useful for combinatorial arguments, |P_n| = (n-1)!/2,
--   and for the uniform barycentre argument (Chapter 7).
--   Used in: N_YisinConv, N_FullDimensional (barycentre).
--
-- ======================================================================

import Mathlib.Tactic
import MembershipProject.Core.N_PedigreeDefinition
import MembershipProject.Core.N_MIRFeasible
import MembershipProject.Core.N_LayeredNetworkTypes

namespace MembershipProject.Core

-- ======================================================================
-- REPRESENTATION 3: PedigreeNode and Tree Definition
-- (from TreeDef.lean, Chapter 1 of Arthanari 2023)
-- ======================================================================

/-- A PedigreeNode is a triangle {i,j,k} with 1≤i<j<k≤n.
    This is a node in the directed graph D+(Δ,A) of Chapter 1. -/
structure PedigreeNode (n : ℕ) where
  i : ℕ
  j : ℕ
  k : ℕ
  h_bound : 1 ≤ i ∧ i < j ∧ j < k ∧ k ≤ n
deriving BEq, DecidableEq, Repr

/-- Macro for clean PedigreeNode construction. -/
macro "pnode" i:term "," j:term "," k:term : term =>
  `(PedigreeNode.mk $i $j $k (by omega))

/-- u is a generator of v in D+(Δ,A) if:
    (1) u.k = max(3, v.j)   — u is at the layer of v's common edge
    (2) u contains v.i       — u shares vertex i with v
    (3) u contains v.j       — u shares vertex j with v
    Reference: Arthanari 2023, Chapter 1, Definition (Generator). -/
def isGeneratorOf {n : ℕ} (u v : PedigreeNode n) : Bool :=
  (u.k == Nat.max 3 v.j) &&
  (u.i == v.i || u.j == v.i || u.k == v.i) &&
  (u.i == v.j || u.j == v.j || u.k == v.j)

/-- A PedigreeTree is a list of PedigreeNodes forming a valid pedigree.
    Conditions (Chapter 1, Definition 1):
    1. Contains root {1,2,3}
    2. All nodes satisfy bounds
    3. Exactly one node per layer k=3,...,n
    4. Every node (k>3) has a generator in the tree
    5. Distinct common edges {i,j}
    Reference: Arthanari 2023, Chapter 1. -/
def isPedigreeTree (n : ℕ) (hn : 3 ≤ n) (nodes : List (PedigreeNode n)) : Bool :=
  -- Condition 1: root {1,2,3} present
  let hasRoot := nodes.contains ⟨1, 2, 3, by omega⟩
  -- Condition 2: all nodes satisfy bounds
  let validBounds := nodes.all fun t =>
    1 ≤ t.i && t.i < t.j && t.j < t.k && t.k ≤ n
  -- Condition 3: exactly one node per layer
  let layers := (List.range (n + 1)).filter (· ≥ 3)
  let exactOnePerLayer := layers.all fun k =>
    (nodes.filter (fun t => t.k == k)).length == 1
  -- Condition 4: every non-root node has a generator
  let validGenerators := nodes.all fun t =>
    if t.k ≤ 3 then true
    else nodes.any fun u => isGeneratorOf u t
  -- Condition 5: distinct common edges {i,j}
  let distinctEdges := nodes.all fun t1 =>
    (nodes.filter (fun t2 => t1.i == t2.i && t1.j == t2.j)).length == 1
  hasRoot && validBounds && exactOnePerLayer && validGenerators && distinctEdges

-- ======================================================================
-- VERIFIED EXAMPLES (results confirmed by #eval):
-- isPedigreeTree 6 [{1,2,3},{1,3,4},{3,4,5},{1,4,6}] = true  ✓
-- isPedigreeTree 5 [{1,2,3},{1,2,4},{3,4,5}]         = false ✓
-- (run #eval outside namespace to check interactively)
-- ======================================================================

-- ======================================================================
-- COMPARISON TABLE (non-executable, for documentation)
-- ======================================================================

/-
SUMMARY: When to use each representation
=========================================

| Representation    | Type              | Computable | Used for                    |
|-------------------|-------------------|------------|-----------------------------|
| Pedigree n        | Prop/struct       | No         | Theorems, hypSum            |
| List (Edge n)     | List              | Yes        | Adjacency, swap             |
| PedigreeTree      | List (PedigreeNode)| Yes       | Chapter 1 def, algorithm    |
| Finset Triple     | Finset            | Yes        | Counting, barycentre        |
| MIR 0-1 solution  | LayeredPoint n    | Yes        | STSP, LemmaOneOne, Ch.3     |

KEY BIJECTIONS (all machine-verified or axiomatised):
  pedigreeToEdges   : Pedigree n → List (Edge n)    [PedigreeBijection.lean]
  edgesToPedigree   : List (Edge n) → Pedigree n    [PedigreeBijection.lean]
  treeToEdges       : PedigreeTree → List (Edge n)  [future work]
  pedigreeToFinset  : Pedigree n → Finset Triple    [N_YisinConv.lean]

The four representations are equivalent — each captures the same
combinatorial object (a Hamiltonian cycle in K_n) from a different
computational or mathematical angle.
-/

-- ======================================================================
-- RANDOM TESTING (from TreeDefRandomTest.lean)
-- ======================================================================

/-- Generate all valid triangle candidates at layer k for a partial tree.
    A candidate is valid if:
    (1) it has a generator in the current tree
    (2) its common edge {i,j} does not clash with existing edges
    Reference: Arthanari 2023, Chapter 5, Construction of layered network. -/
def validCandidatesAt (n : ℕ) (k : ℕ) (_hk : k ≤ n)
    (tree : List (PedigreeNode n)) : List (PedigreeNode n) :=
  Id.run do
    let mut candidates : List (PedigreeNode n) := []
    for j in List.range k do
      for i in List.range j do
        if h : 1 ≤ i + 1 ∧ i + 1 < j + 1 ∧ j + 1 < k ∧ k ≤ n then
          let v : PedigreeNode n := ⟨i + 1, j + 1, k, h⟩
          let hasGen  := tree.any (fun u => isGeneratorOf u v)
          let noClash := tree.all (fun u => u.i ≠ v.i || u.j ≠ v.j)
          if hasGen && noClash then
            candidates := candidates ++ [v]
    return candidates


-- ======================================================================
-- REPRESENTATION 5: MIR 0-1 Solution (Characteristic Vector)
-- Chapter 3 (Arthanari 1983), N_LemmaOneOne.lean, N_YisinMI.lean
-- ======================================================================

/-- Representation 5: A pedigree P ∈ Pₙ has a characteristic vector
    X^P ∈ {0,1}^{τ_n}, the MIR 0-1 solution, defined by:
      X^P_{ijk} = 1  iff  {i,j,k} ∈ P
      X^P_{ijk} = 0  otherwise

    This is a VERTEX of conv(Pₙ) — an extreme point of the polytope.

    KEY CONNECTIONS:
    (a) MI-formulation (Chapter 3, Arthanari 1983):
        Minimising Σ c_{ijk} X_{ijk} over conv(Pₙ) solves STSP.
        The objective coefficients c_{ijk} = d_{ik} + d_{jk} - d_{ij}
        encode the incremental insertion cost of city k between i and j.

    (b) LemmaOneOne (N_LemmaOneOne.lean):
        An integer solution X ∈ {0,1}^{τ_n} to MIR(n) corresponds
        to a unique Hamiltonian tour (pedigree) in P_n.
        Proved: theorem lemma_oneone (0 sorries).

    (c) Y^s ∈ P_MI(k) (N_YisinMI.lean):
        From a feasible MCF(k) solution, the commodity flow Y^s
        satisfies (1/v^s)Y^s ∈ P_MI(k) — a fractional MIR solution.
        This is the bridge from MCF feasibility to conv(Pₙ) membership.
        Proved: theorem Y_s_in_PMI (0 sorries).

    (d) P=NP chain (N_PEqualsNP.lean):
        STSP optimisation = minimise MI-objective over conv(Pₙ).
        M3P ∈ P → polynomial optimisation over conv(Pₙ) → STSP ∈ P.
        Reference: Arthanari 1983, Chapter 3 of Pedigree Polytopes.

    TYPE in Lean 4: LayeredPoint n := Triple → ℚ
    A characteristic vector is a LayeredPoint n with values in {0,1}.
    MIR feasibility: MIRFeasible n (N_MIRFeasible.lean). -/
def isMIR01Solution {n : ℕ} (X : LayeredPoint n) : Prop :=
  ∀ t : Triple, X t = 0 ∨ X t = 1

/-- A pedigree P ∈ Pₙ gives a MIR 0-1 solution via its characteristic
    vector. This is the vertex of conv(Pₙ) corresponding to P.
    The characteristic vector has exactly one 1 per layer k=4,...,n
    (at the triangle chosen by P at layer k) and 0 elsewhere. -/
def characteristicVector {n : ℕ} (P : Pedigree n) : LayeredPoint n :=
  fun t => if t ∈ P.triangles then 1 else 0

/-- The characteristic vector of a pedigree is a MIR 0-1 solution. -/
theorem characteristicVector_is_01 {n : ℕ} (P : Pedigree n) :
    isMIR01Solution (characteristicVector P) := by
  intro t
  simp [characteristicVector]
  tauto

end MembershipProject.Core
