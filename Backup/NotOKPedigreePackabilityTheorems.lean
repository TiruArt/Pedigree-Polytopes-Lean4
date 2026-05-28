-- Core\PedigreePackabilityTheorems.lean
import MembershipProject.Core.Basic
import MembershipProject.Core.MatrixOps
import MembershipProject.Core.Restriction
import MembershipProject.Core.Types


namespace MembershipProject.Core

open Nat

-- =============================================================================
-- SECTION 1: BASIC DEFINITIONS
-- =============================================================================

def initialSlack : SlackVector 3 := fun _ => (1 : Rat)

structure MIRStructure (n : Nat) where
  P : ∀ (k : Nat), 3 ≤ k → k ≤ n → GenVector k
  nonneg : ∀ (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n) (v : GenVar k),
    P k hk3 hkn v ≥ (0 : Rat)

-- =============================================================================
-- SECTION 2: SLACK COMPUTATION
-- =============================================================================

def computeSlackSparse (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n) : SlackVector k :=
  if h : k = 3 then
    h ▸ initialSlack
  else
    have hk_prev : 3 ≤ k - 1 := by omega
    have hkn_prev : k - 1 ≤ n := by omega
    let U_prev := computeSlackSparse n mir (k - 1) hk_prev hkn_prev
    let A_k : SparseGenerationMatrix k := ⟨hk3⟩
    let P_k := mir.P k hk3 hkn
    fun e =>
      if hj : e.j < k - 1 then
        have hi_prev : e.i < k - 1 := by
          have h1 : e.i < e.j := e.hij
          have h2 : e.j < k - 1 := hj
          omega
        let e_prev : Edge (k - 1) := ⟨e.i, e.j, hi_prev, hj, e.hij⟩
        U_prev e_prev - sparseMatVecMul k A_k P_k e
      else
        (0 : Rat) - sparseMatVecMul k A_k P_k e
termination_by k
decreasing_by omega

-- =============================================================================
-- SECTION 3: BASIC THEOREMS
-- =============================================================================

theorem computeSlackSparse_base_case (n : Nat) (mir : MIRStructure n)
    (hn : n ≥ 3) (e : Edge 3) :
    computeSlackSparse n mir 3 (by omega) (by omega) e = initialSlack e := by
  unfold computeSlackSparse
  simp

theorem computeSlackSparse_old_edge (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk : k ≥ 4) (hkn : k ≤ n) (e : Edge k)
    (h_old : e.j < k - 1) :
    let A_k : SparseGenerationMatrix k := ⟨by omega⟩
    let P_k := mir.P k (by omega) hkn
    computeSlackSparse n mir k (by omega) hkn e =
    computeSlackSparse n mir (k - 1) (by omega) (by omega : k - 1 ≤ n)
      ⟨e.i, e.j, by have h1 : e.i < e.j := e.hij; omega, h_old, e.hij⟩ -
    sparseMatVecMul k A_k P_k e := by
  conv_lhs => unfold computeSlackSparse
  simp [show k ≠ 3 by omega, h_old]

theorem computeSlackSparse_new_edge (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk : k ≥ 4) (hkn : k ≤ n) (e : Edge k)
    (h_new : e.j = k - 1) :
    computeSlackSparse n mir k (by omega) hkn e =
    0 - sparseMatVecMul k ⟨by omega⟩ (mir.P k (by omega) hkn) e := by
  unfold computeSlackSparse
  have h_not_old : ¬(e.j < k - 1) := by omega
  simp only [show k ≠ 3 by omega, ↓reduceDIte, h_not_old, ↓reduceDIte]

theorem computeSlackSparse_correct_step_old (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk : k ≥ 4) (hkn : k ≤ n) (edge : Edge k) (h_old : edge.j < k - 1) :
    let A_k : SparseGenerationMatrix k := ⟨by omega⟩
    let P_k := mir.P k (by omega) hkn
    computeSlackSparse n mir k (by omega) hkn edge =
    computeSlackSparse n mir (k - 1) (by omega) (by omega : k - 1 ≤ n)
      ⟨edge.i, edge.j, by have h1 : edge.i < edge.j := edge.hij; omega, h_old, edge.hij⟩ -
    sparseMatVecMul k A_k P_k edge :=
  computeSlackSparse_old_edge n mir k hk hkn edge h_old

theorem computeSlackSparse_correct_step_new (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk : k ≥ 4) (hkn : k ≤ n) (edge : Edge k) (h_new : edge.j ≥ k - 1) :
    computeSlackSparse n mir k (by omega) hkn edge =
    0 - sparseMatVecMul k ⟨by omega⟩ (mir.P k (by omega) hkn) edge := by
  have h_eq : edge.j = k - 1 := by
    have hj : edge.j < k := edge.hj
    omega
  exact computeSlackSparse_new_edge n mir k hk hkn edge h_eq

theorem computeSlackSparse_correct_step (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk : k ≥ 4) (hkn : k ≤ n) (edge : Edge k) :
    if h : edge.j < k - 1 then
      let A_k : SparseGenerationMatrix k := ⟨by omega⟩
      let P_k := mir.P k (by omega) hkn
      computeSlackSparse n mir k (by omega) hkn edge =
      computeSlackSparse n mir (k - 1) (by omega) (by omega : k - 1 ≤ n)
        ⟨edge.i, edge.j, by have h1 : edge.i < edge.j := edge.hij; omega, h, edge.hij⟩ -
      sparseMatVecMul k A_k P_k edge
    else
      computeSlackSparse n mir k (by omega) hkn edge =
      0 - sparseMatVecMul k ⟨by omega⟩ (mir.P k (by omega) hkn) edge := by
  split
  case isTrue h_old =>
    exact computeSlackSparse_correct_step_old n mir k hk hkn edge h_old
  case isFalse h_new =>
    have h_ge : edge.j ≥ k - 1 := by omega
    exact computeSlackSparse_correct_step_new n mir k hk hkn edge h_ge

-- =============================================================================
-- SECTION 4: NETWORK STRUCTURE WITH RESTRICTIONS
-- =============================================================================

structure Link (n : Nat) where
  k : Nat
  i : Nat
  j : Nat
  a : Nat
  b : Nat
  hk : k ≥ 3
  hkn : k < n
  hij : i < j
  hj : j < k
  hab : a < b
  hb : b < k + 1

def Link.toTriples (L : Link n) : Triple × Triple :=
  (⟨L.i, L.j, L.k, L.hij, L.hj⟩, ⟨L.a, L.b, L.k + 1, L.hab, L.hb⟩)

structure RestrictedNetwork (n : Nat) (L : Link n) where
  k_ge_5 : L.k ≥ 5
  baseCaps : NodeCapacities
  D : Finset Triple :=
    let (t1, t2) := L.toTriples
    Restriction.computeD t1 t2
  restrictedCaps : NodeCapacities :=
    Restriction.restrictCapacities baseCaps D

-- =============================================================================
-- SECTION 5: PEDIGREE FRAMEWORK WITH PARTITION STRUCTURE
-- =============================================================================

structure Pedigree (n : Nat) where
  edges : ∀ (k : Nat), 3 ≤ k → k ≤ n → Edge k
  coherent : ∀ (k : Nat) (hk3 : 3 ≤ k) (hkn : k < n),
    ∃ (L : Link n), L.k = k ∧
    L.i = (edges k hk3 (by omega)).i ∧
    L.j = (edges k hk3 (by omega)).j ∧
    L.a = (edges (k+1) (by omega) (by omega)).i ∧
    L.b = (edges (k+1) (by omega) (by omega)).j

def Pedigree.endsAtNode (r : Pedigree n) (l : Nat) (h3 : 3 ≤ l) (hn : l ≤ n)
    (node : Node) : Prop :=
  let e := r.edges l h3 hn
  e.i = node.i ∧ e.j = node.j ∧ l = node.k

def Pedigrees_k (n : Nat) (k : Nat) (hk : k ≤ n) : Set (Pedigree n) :=
  { r | ∀ (j : Nat) (hj3 : 3 ≤ j) (hjk : j ≤ k), True }

def I_edge (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n) (e : Edge k) : Set (Pedigree n) :=
  { r | r.edges k hk3 hkn = e }

def J_edge (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n) (e : Edge k) : Set (Pedigree n) :=
  { r | edge_in_hamiltonian_cycle r k e }
  where
    edge_in_hamiltonian_cycle (r : Pedigree n) (k : Nat) (e : Edge k) : Prop := sorry

def J_link (n : Nat) (L : Link n) : Set (Pedigree n) :=
  { r | ∃ (hk3 : 3 ≤ L.k) (hkn : L.k ≤ n) (hk3' : 3 ≤ L.k + 1) (hkn' : L.k + 1 ≤ n),
    (r.edges L.k hk3 hkn).i = L.i ∧
    (r.edges L.k hk3 hkn).j = L.j ∧
    (r.edges (L.k + 1) hk3' hkn').i = L.a ∧
    (r.edges (L.k + 1) hk3' hkn').j = L.b }

structure PedigreeWeights (n : Nat) where
  λ : Pedigree n → Rat
  nonneg : ∀ r, λ r ≥ 0

-- =============================================================================
-- PARTITION STRUCTURE THEOREMS
-- =============================================================================

theorem I_edge_partition (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n) :
    (∀ (e1 e2 : Edge k), e1 ≠ e2 → Disjoint (I_edge n k hk3 hkn e1) (I_edge n k hk3 hkn e2)) ∧
    (∀ (r : Pedigree n), ∃ (e : Edge k), r ∈ I_edge n k hk3 hkn e) := by
  constructor
  · intros e1 e2 h_ne
    unfold I_edge
    simp [Set.disjoint_iff_forall_ne]
    intros r hr1 r' hr2
    intro h_eq
    subst h_eq
    have : e1 = r.edges k hk3 hkn := hr1
    have : e2 = r.edges k hk3 hkn := hr2
    subst_vars
    exact h_ne rfl
  · intro r
    use r.edges k hk3 hkn
    unfold I_edge
    simp

theorem partition_sum_equals_generation (n : Nat) (mir : MIRStructure n)
    (weights : PedigreeWeights n) (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n)
    (e : Edge k)
    (h_conv : inConvexHull n mir k hk3 hkn) :
    ∑' (r : I_edge n k hk3 hkn e), weights.λ r.val =
    mir.P k hk3 hkn ⟨e.i, e.j, e.hij⟩ := by
  sorry
  where
    inConvexHull (n : Nat) (mir : MIRStructure n) (k : Nat)
        (hk3 : 3 ≤ k) (hkn : k ≤ n) : Prop := sorry

theorem J_edge_partition_by_source (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n)
    (e_target : Edge k) :
    J_edge n k hk3 hkn e_target =
    ⋃ (e_source : Edge k), (I_edge n k hk3 hkn e_source ∩ J_edge n k hk3 hkn e_target) := by
  unfold J_edge I_edge
  ext r
  simp
  constructor
  · intro hr_in_HC
    use r.edges k hk3 hkn
    constructor
    · rfl
    · exact hr_in_HC
  · intro ⟨e_source, h_ends, h_in_HC⟩
    exact h_in_HC

theorem I_J_disjoint (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n) (e : Edge k) :
    Disjoint (I_edge n k hk3 hkn e) (J_edge n k hk3 hkn e) := by
  sorry

theorem J_edge_partition_disjoint (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n)
    (e_target : Edge k) (e1 e2 : Edge k) (h_ne : e1 ≠ e2) :
    Disjoint
      (I_edge n k hk3 hkn e1 ∩ J_edge n k hk3 hkn e_target)
      (I_edge n k hk3 hkn e2 ∩ J_edge n k hk3 hkn e_target) := by
  have h_disj := (I_edge_partition n k hk3 hkn).1 e1 e2 h_ne
  exact Set.disjoint_inter_of_disjoint_left h_disj

theorem I_or_J_not_both (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n)
    (e : Edge k) (r : Pedigree n) :
    ¬(r ∈ I_edge n k hk3 hkn e ∧ r ∈ J_edge n k hk3 hkn e) := by
  intro ⟨h1, h2⟩
  have h_disj := I_J_disjoint n k hk3 hkn e
  exact Set.disjoint_iff_forall_ne.mp h_disj r h1 r h2 rfl

-- =============================================================================
-- TWO-LAYER BIPARTITE FLOW STRUCTURE
-- =============================================================================

-- THEOREM: Active pedigrees can be partitioned by layer k OR by layer k+1
theorem two_layer_partition (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k+1 ≤ n)
    (weights : PedigreeWeights n) :
    let I_active := ActivePedigrees n (k+1) hkn weights
    -- Partition by layer k (sources)
    (I_active = ⋃ (e : Edge k), S_O n k hk3 (by omega) e weights) ∧
    -- Partition by layer k+1 (sinks)
    (I_active = ⋃ (e' : Edge (k+1)), S_D n k hk3 hkn e' weights) := by
  sorry

-- Supply at source e (layer k): sum of weights of pedigrees using edge e
-- FINITE SUM over S_O(e)
def supply (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n)
    (e : Edge k) (weights : PedigreeWeights n) : Rat :=
  let S := S_O n k hk3 hkn e weights
  let h_fin := S_O_finite n k hk3 hkn e weights
  ∑ r in h_fin.toFinset, weights.λ r

-- Demand at sink e' (layer k+1): sum of weights of pedigrees using edge e'
-- FINITE SUM over S_D(e')
def demand (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k+1 ≤ n)
    (e' : Edge (k+1)) (weights : PedigreeWeights n) : Rat :=
  let S := S_D n k hk3 hkn e' weights
  let h_fin := S_D_finite n k hk3 hkn e' weights
  ∑ r in h_fin.toFinset, weights.λ r

-- Arc (e, e') is ALLOWED iff some active pedigree uses both edges
def arcAllowed (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k+1 ≤ n)
    (e : Edge k) (e' : Edge (k+1)) (weights : PedigreeWeights n) : Prop :=
  (S_O n k hk3 (by omega) e weights ∩ S_D n k hk3 hkn e' weights).Nonempty

-- Flow on arc (e, e'): sum of weights of pedigrees using BOTH edges
-- FINITE SUM over S_O(e) ∩ S_D(e')
def bipartiteFlow (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k+1 ≤ n)
    (e : Edge k) (e' : Edge (k+1)) (weights : PedigreeWeights n) : Rat :=
  let S := S_O n k hk3 (by omega) e weights ∩ S_D n k hk3 hkn e' weights
  let h_fin := Set.Finite.subset (S_O_finite n k hk3 (by omega) e weights) (Set.inter_subset_left _ _)
  ∑ r in h_fin.toFinset, weights.λ r

-- LEMMA: Helper for partition-based sum reordering
-- When S_O(e) is partitioned by S_D(e'), we can reorder the sum
-- Since these are FINITE sums, this is straightforward
lemma sum_over_partition_source (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k+1 ≤ n)
    (e : Edge k) (weights : PedigreeWeights n)
    (edges_k_plus_1 : Finset (Edge (k+1))) :
    ∑ e' in edges_k_plus_1, bipartiteFlow n k hk3 hkn e e' weights =
    supply n k hk3 (by omega) e weights := by
  unfold bipartiteFlow supply
  -- The key: S_O(e) = ⊔_{e'} (S_O(e) ∩ S_D(e'))
  -- For finite sets, sum over partition equals sum over whole set
  sorry

lemma sum_over_partition_sink (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k+1 ≤ n)
    (e' : Edge (k+1)) (weights : PedigreeWeights n)
    (edges_k : Finset (Edge k)) :
    ∑ e in edges_k, bipartiteFlow n k hk3 hkn e e' weights =
    demand n k hk3 hkn e' weights := by
  unfold bipartiteFlow demand
  -- The key: S_D(e') = ⊔_{e} (S_O(e) ∩ S_D(e'))
  -- For finite sets, sum over partition equals sum over whole set
  sorry

-- THEOREM: The bipartite flow is feasible
-- Flow conservation holds at all sources and sinks
-- WLOG: We only consider edges with positive capacity (supply > 0 or demand > 0)
theorem bipartite_flow_feasible (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk3 : 3 ≤ k) (hkn : k+1 ≤ n)
    (weights : PedigreeWeights n)
    (h_conv : inConvexHull n mir (k+1) (by omega) hkn)
    (edges_k : Finset (Edge k))
    (edges_k_plus_1 : Finset (Edge (k+1))) :
    -- Flow conservation at sources (outflow = supply)
    (∀ (e : Edge k) (h_pos : supply n k hk3 (by omega) e weights > 0),
      ∑ e' in edges_k_plus_1, bipartiteFlow n k hk3 hkn e e' weights =
      supply n k hk3 (by omega) e weights) ∧
    -- Flow conservation at sinks (inflow = demand)
    (∀ (e' : Edge (k+1)) (h_pos : demand n k hk3 hkn e' weights > 0),
      ∑ e in edges_k, bipartiteFlow n k hk3 hkn e e' weights =
      demand n k hk3 hkn e' weights) := by
  constructor
  · -- Source conservation: ∑_{e'} f_{e,e'} = supply(e)
    intros e h_pos
    exact sum_over_partition_source n k hk3 hkn e weights edges_k_plus_1
  · -- Sink conservation: ∑_{e} f_{e,e'} = demand(e')
    intros e' h_pos
    exact sum_over_partition_sink n k hk3 hkn e' weights edges_k

-- LEMMA: Edges with zero supply/demand are trivially satisfied
theorem zero_capacity_trivial (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k+1 ≤ n)
    (weights : PedigreeWeights n) :
    -- If supply = 0, then no flow leaves e
    (∀ (e : Edge k), supply n k hk3 (by omega) e weights = 0 →
      ∀ (e' : Edge (k+1)), bipartiteFlow n k hk3 hkn e e' weights = 0) ∧
    -- If demand = 0, then no flow enters e'
    (∀ (e' : Edge (k+1)), demand n k hk3 hkn e' weights = 0 →
      ∀ (e : Edge k), bipartiteFlow n k hk3 hkn e e' weights = 0) := by
  constructor
  · -- Zero supply case
    intros e h_zero e'
    unfold bipartiteFlow supply at *
    sorry
  · -- Zero demand case
    intros e' h_zero e
    unfold bipartiteFlow demand at *
    sorry

-- THEOREM: Supply equals demand (total flow balance)
-- This follows from the fact that both equal ∑_r λ_r over active pedigrees
theorem supply_equals_demand (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k+1 ≤ n)
    (weights : PedigreeWeights n)
    (edges_k : Finset (Edge k))
    (edges_k_plus_1 : Finset (Edge (k+1))) :
    ∑ e in edges_k, supply n k hk3 (by omega) e weights =
    ∑ e' in edges_k_plus_1, demand n k hk3 hkn e' weights := by
  -- Both sides equal ∑_{r ∈ ActivePedigrees} λ_r
  sorry

-- COROLLARY: If arc (e, e') is forbidden, then no flow on that arc
theorem forbidden_arc_zero_flow (n : Nat) (k : Nat) (hk3 : 3 ≤ k) (hkn : k+1 ≤ n)
    (e : Edge k) (e' : Edge (k+1)) (weights : PedigreeWeights n)
    (h_forbidden : ¬arcAllowed n k hk3 hkn e e' weights) :
    bipartiteFlow n k hk3 hkn e e' weights = 0 := by
  sorry

-- =============================================================================
-- SECTION 6: CONVEX HULL CHARACTERIZATION
-- =============================================================================

def inConvexHull (n : Nat) (mir : MIRStructure n) (k : Nat)
    (hk3 : 3 ≤ k) (hkn : k ≤ n) : Prop :=
  ∃ (weights : PedigreeWeights n),
    (∑' r, weights.λ r = 1) ∧
    (∀ (v : GenVar k), mir.P k hk3 hkn v =
      ∑' (r : Pedigrees_k n k hkn), weights.λ r.val * (pedigreeIndicator r.val k v))
  where
    pedigreeIndicator (r : Pedigree n) (k : Nat) (v : GenVar k) : Rat := sorry

-- =============================================================================
-- SECTION 7: BASE CASES
-- =============================================================================

theorem base_case_k3 (n : Nat) (mir : MIRStructure n) (hn : n ≥ 3) :
    inConvexHull n mir 3 (by omega) (by omega) := by
  sorry

structure F4ArcRestriction where
  rule_a : ∀ (src tgt : Edge 4), src.i ≠ tgt.i ∨ src.j ≠ tgt.j
  rule_b : ∀ (src : Edge 4) (tgt : Node),
    tgt.k = 5 → tgt.j > 3 → (tgt.i = src.i ∨ tgt.i = src.j)

theorem base_case_k4 (n : Nat) (mir : MIRStructure n) (hn : n ≥ 4)
    (h_feasible : ∀ (e : Edge 4), computeSlackSparse n mir 4 (by omega) (by omega) e ≥ 0)
    (h_maxflow : maxFlowAtLayer4 n mir = 1) :
    inConvexHull n mir 4 (by omega) (by omega) := by
  sorry
  where
    maxFlowAtLayer4 (n : Nat) (mir : MIRStructure n) : Rat := sorry

theorem base_case_k5 (n : Nat) (mir : MIRStructure n) (hn : n ≥ 5)
    (h_feasible : ∀ (e : Edge 5), computeSlackSparse n mir 5 (by omega) (by omega) e ≥ 0)
    (h_maxflow : maxFlowAtLayer5 n mir = 1) :
    inConvexHull n mir 5 (by omega) (by omega) := by
  sorry
  where
    maxFlowAtLayer5 (n : Nat) (mir : MIRStructure n) : Rat := sorry

-- =============================================================================
-- SECTION 8: FLOW DECOMPOSITION
-- =============================================================================

def flowAlongLink (n : Nat) (mir : MIRStructure n) (L : Link n)
    (net : RestrictedNetwork n L) : Rat :=
  sorry

def maxFlowRestricted (n : Nat) (L : Link n) (net : RestrictedNetwork n L) : Rat :=
  sorry

def pathAvailableInRestricted (n : Nat) (L : Link n) (net : RestrictedNetwork n L)
    (r : Pedigree n) : Prop :=
  sorry

def isRigidPedigree (n : Nat) (r : Pedigree n) (k : Nat) : Prop :=
  sorry

theorem active_pedigree_path_available (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk : k ≥ 5) (hkn : k < n) (L : Link n) (hLk : L.k = k)
    (net : RestrictedNetwork n L)
    (r : Pedigree n) (h_active : r ∈ Pedigrees_k n k (by omega))
    (weights : PedigreeWeights n) (h_pos : weights.λ r > 0) :
    pathAvailableInRestricted n L net r ∨ isRigidPedigree n r k := by
  sorry

def extendablePedigrees (n : Nat) (L : Link n) : Set (Pedigree n) :=
  let hk3 : 3 ≤ L.k := by omega
  let hkn : L.k ≤ n := by omega
  let hk3' : 3 ≤ L.k + 1 := by omega
  let hkn' : L.k + 1 ≤ n := by omega
  let e_src : Edge L.k := ⟨L.i, L.j,
    by have := L.hij; have := L.hj; omega,
    L.hj,
    L.hij⟩
  let e_tgt : Edge (L.k + 1) := ⟨L.a, L.b,
    by have := L.hab; have := L.hb; omega,
    L.hb,
    L.hab⟩
  I_edge n L.k hk3 hkn e_src ∩ J_edge n (L.k + 1) hk3' hkn' e_tgt

theorem pedigrees_extendable_through_link (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk : k ≥ 5) (hkn : k < n) (L : Link n) (hLk : L.k = k)
    (net : RestrictedNetwork n L)
    (r : Pedigree n) (h_in_P : r ∈ extendablePedigrees n L)
    (weights : PedigreeWeights n) (h_pos : weights.λ r > 0) :
    ∃ (r_extended : Pedigree n),
      r_extended ∈ Pedigrees_k n (k+1) (by omega) ∧
      (r_extended.edges (k+1) (by omega) (by omega)).i = L.a ∧
      (r_extended.edges (k+1) (by omega) (by omega)).j = L.b ∧
      (∀ (j : Nat) (hj3 : 3 ≤ j) (hjk : j ≤ k),
        r_extended.edges j hj3 (by omega) = r.edges j hj3 (by omega)) := by
  sorry

theorem node_capacity_conservation (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk : k ≥ 5) (hkn : k < n)
    (pedigrees : Finset (Pedigree n))
    (weights : PedigreeWeights n)
    (δ : Pedigree n → Rat)
    (caps : NodeCapacities)
    (h_capacity_saturated :
      ∀ (l : Nat) (hl3 : 3 ≤ l) (hln : l ≤ k) (t : Triple) (ht : t.k = l),
        ∑ r in pedigrees.filter (λ r => r.endsAtNode l hl3 (by omega) t.toNode),
          weights.λ r = caps.caps t)
    (h_delta_le_lambda : ∀ r ∈ pedigrees, δ r ≤ weights.λ r) :
    ∀ (l : Nat) (hl3 : 3 ≤ l) (hln : l ≤ k + 1) (t : Triple) (ht : t.k = l),
      ∑ r in pedigrees.filter (λ r => r.endsAtNode l hl3 (by omega) t.toNode),
        δ r ≤ caps.caps t := by
  sorry

end MembershipProject.Core
