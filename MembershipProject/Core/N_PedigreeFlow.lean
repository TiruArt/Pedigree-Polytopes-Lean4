import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import MembershipProject.Core.N_PartitionFlow  -- Import our basic lemma

/-!
# Application: Pedigree Polytope Bipartite Flow

This file demonstrates how the abstract Partition Probability Flow theorem
applies to prove feasibility of bipartite flows in pedigree polytopes.

## The Setup

Given a pedigree structure with:
- Pedigrees R with weights λ_r (summing to 1)
- Layer k edges that partition pedigrees via S_O(e)
- Layer k+1 edges that partition pedigrees via S_D(e')

We show that the flow f_{e,e'} = ∑_{r ∈ S_O(e) ∩ S_D(e')} λ_r
is feasible by applying prob_partition_is_feasible_flow.

## Mathematical Insight

The key insight is that the pedigree flow problem is **exactly** an instance
of the partition probability flow problem:

- **Domain D**: The set of all pedigrees (with positive weight)
- **Partition D₁**: Partition of pedigrees by layer-k edges (via S_O)
- **Partition D₂**: Partition of pedigrees by layer-(k+1) edges (via S_D)
- **Probability p**: The normalized weights λ_r
- **Flow formula**: f(e, e') = ∑_{r ∈ S_O(e) ∩ S_D(e')} λ_r

This connection shows that pedigree polytope feasibility is fundamentally
about probability distributions over partition refinements.
-/

open Finset BigOperators

/-
  Pedigree structure (simplified for this application)
  We use a finite type R for pedigrees
-/
structure PedigreeStructure (R : Type*) [DecidableEq R] [Fintype R] (n : ℕ) where
  -- The set of all pedigrees
  pedigrees : Finset R
  -- Weights for each pedigree (convex combination)
  weights : R → ℝ
  h_nonneg : ∀ r ∈ pedigrees, 0 ≤ weights r
  h_sum_one : ∑ r ∈ pedigrees, weights r = 1
  h_support : ∀ r ∉ pedigrees, weights r = 0

/-
  Edge at a given layer
-/
structure Edge (k : ℕ) where
  node1 : ℕ
  node2 : ℕ
  h_layer : node1 < node2  -- simplified constraint

/-
  Layer structure: edges at layers k and k+1

  This structure captures how pedigrees are partitioned by edges at two consecutive layers.
  Each edge determines which pedigrees pass through it.
-/
structure LayerStructure (R : Type*) [DecidableEq R] [Fintype R]
    (n k : ℕ) (ped : PedigreeStructure R n) where
  edges_k : Finset (Edge k)
  edges_k1 : Finset (Edge (k+1))
  -- For each edge at layer k, which pedigrees use it as origin
  S_O : Edge k → Finset R
  -- For each edge at layer k+1, which pedigrees use it as destination
  S_D : Edge (k+1) → Finset R
  -- S_O partitions the pedigrees
  h_S_O_nonempty : ∀ e ∈ edges_k, (S_O e).Nonempty
  h_S_O_disjoint : ∀ e₁ ∈ edges_k, ∀ e₂ ∈ edges_k,
    e₁ ≠ e₂ → Disjoint (S_O e₁) (S_O e₂)
  h_S_O_covers : ∀ r ∈ ped.pedigrees, ∃ e ∈ edges_k, r ∈ S_O e
  h_S_O_subsets : ∀ e ∈ edges_k, S_O e ⊆ ped.pedigrees
  -- S_D partitions the pedigrees
  h_S_D_nonempty : ∀ e ∈ edges_k1, (S_D e).Nonempty
  h_S_D_disjoint : ∀ e₁ ∈ edges_k1, ∀ e₂ ∈ edges_k1,
    e₁ ≠ e₂ → Disjoint (S_D e₁) (S_D e₂)
  h_S_D_covers : ∀ r ∈ ped.pedigrees, ∃ e ∈ edges_k1, r ∈ S_D e
  h_S_D_subsets : ∀ e ∈ edges_k1, S_D e ⊆ ped.pedigrees

variable {R : Type*} [DecidableEq R] [Fintype R]

/-
  Convert PedigreeStructure to ProbDist

  This is the key translation: pedigree weights form a probability distribution
-/
def pedigree_to_probdist {n : ℕ} (ped : PedigreeStructure R n) :
    ProbDist ped.pedigrees where
  prob := ped.weights
  h_nonneg := ped.h_nonneg
  h_sum_one := ped.h_sum_one
  h_support := ped.h_support

/-
  Convert S_O to a partition

  This shows that the collection of S_O(e) for all edges e forms a partition
  of the pedigree set.
-/
def S_O_partition {n k : ℕ} {ped : PedigreeStructure R n}
    (layer : LayerStructure R n k ped) :
    FinsetPartition ped.pedigrees where
  parts := layer.edges_k.image layer.S_O
  h_nonempty := by
    intro s hs
    rw [Finset.mem_image] at hs
    match hs with
    | ⟨e, he, heq⟩ =>
      rw [← heq]
      exact layer.h_S_O_nonempty e he
  h_disjoint := by
    intro s₁ hs₁ s₂ hs₂ hne
    rw [Finset.mem_image] at hs₁ hs₂
    match hs₁, hs₂ with
    | ⟨e₁, he₁, heq₁⟩, ⟨e₂, he₂, heq₂⟩ =>
      rw [← heq₁, ← heq₂]
      have e_ne : e₁ ≠ e₂ := by
        intro heq
        apply hne
        rw [← heq₁, ← heq₂, heq]
      exact layer.h_S_O_disjoint e₁ he₁ e₂ he₂ e_ne
  h_covers := by
    intro r hr
    obtain ⟨e, he, hr_in⟩ := layer.h_S_O_covers r hr
    use layer.S_O e
    constructor
    · rw [Finset.mem_image]
      exact ⟨e, he, rfl⟩
    · exact hr_in
  h_subsets := by
    intro s hs
    rw [Finset.mem_image] at hs
    match hs with
    | ⟨e, he, heq⟩ =>
      rw [← heq]
      exact layer.h_S_O_subsets e he

/-
  Convert S_D to a partition

  Similarly, S_D(e') for all edges e' at layer k+1 forms a partition.
-/
def S_D_partition {n k : ℕ} {ped : PedigreeStructure R n}
    (layer : LayerStructure R n k ped) :
    FinsetPartition ped.pedigrees where
  parts := layer.edges_k1.image layer.S_D
  h_nonempty := by
    intro s hs
    rw [Finset.mem_image] at hs
    match hs with
    | ⟨e, he, heq⟩ =>
      rw [← heq]
      exact layer.h_S_D_nonempty e he
  h_disjoint := by
    intro s₁ hs₁ s₂ hs₂ hne
    rw [Finset.mem_image] at hs₁ hs₂
    match hs₁, hs₂ with
    | ⟨e₁, he₁, heq₁⟩, ⟨e₂, he₂, heq₂⟩ =>
      rw [← heq₁, ← heq₂]
      have e_ne : e₁ ≠ e₂ := by
        intro heq
        apply hne
        rw [← heq₁, ← heq₂, heq]
      exact layer.h_S_D_disjoint e₁ he₁ e₂ he₂ e_ne
  h_covers := by
    intro r hr
    obtain ⟨e, he, hr_in⟩ := layer.h_S_D_covers r hr
    use layer.S_D e
    constructor
    · rw [Finset.mem_image]
      exact ⟨e, he, rfl⟩
    · exact hr_in
  h_subsets := by
    intro s hs
    rw [Finset.mem_image] at hs
    match hs with
    | ⟨e, he, heq⟩ =>
      rw [← heq]
      exact layer.h_S_D_subsets e he

/-
  Supply at an origin edge e: sum of weights over pedigrees using e
-/
def supply {n k : ℕ} (ped : PedigreeStructure R n)
    (layer : LayerStructure R n k ped) (e : Edge k) : ℝ :=
  ∑ r ∈ layer.S_O e, ped.weights r

/-
  Demand at a sink edge e': sum of weights over pedigrees using e'
-/
def demand {n k : ℕ} (ped : PedigreeStructure R n)
    (layer : LayerStructure R n k ped) (e' : Edge (k+1)) : ℝ :=
  ∑ r ∈ layer.S_D e', ped.weights r

/-
  Flow on arc (e, e'): sum of weights over intersection

  This is the key formula: flow equals the probability mass of pedigrees
  that use both edge e at layer k and edge e' at layer k+1
-/
def pedigree_flow {n k : ℕ} (ped : PedigreeStructure R n)
    (layer : LayerStructure R n k ped)
    (e : Edge k) (e' : Edge (k+1)) : ℝ :=
  ∑ r ∈ (layer.S_O e ∩ layer.S_D e'), ped.weights r

/-!
## Main Theorem: Pedigree Flow Feasibility via Partition Probability

This theorem shows that the pedigree bipartite flow is feasible
by applying the abstract prob_partition_is_feasible_flow theorem.

The proof strategy:
1. Convert pedigree structures to partition/probability structures
2. Apply the abstract theorem to get a feasible flow
3. Show that this abstract flow matches our pedigree flow formula
4. Conclude all four flow properties hold
-/
theorem pedigree_bipartite_flow_feasible
    {n k : ℕ}
    (ped : PedigreeStructure R n)
    (layer : LayerStructure R n k ped) :
    -- Flow conservation at origins (outflow = supply)
    (∀ e ∈ layer.edges_k,
      ∑ e' ∈ layer.edges_k1, pedigree_flow ped layer e e' =
      supply ped layer e) ∧
    -- Flow conservation at sinks (inflow = demand)
    (∀ e' ∈ layer.edges_k1,
      ∑ e ∈ layer.edges_k, pedigree_flow ped layer e e' =
      demand ped layer e') ∧
    -- Non-negativity
    (∀ e ∈ layer.edges_k, ∀ e' ∈ layer.edges_k1,
      0 ≤ pedigree_flow ped layer e e') ∧
    -- Arc structure: flow is zero iff intersection is empty
    (∀ e ∈ layer.edges_k, ∀ e' ∈ layer.edges_k1,
      layer.S_O e ∩ layer.S_D e' = ∅ → pedigree_flow ped layer e e' = 0) := by

  -- Convert pedigree structures to partition probability structures
  let D := ped.pedigrees
  let p := pedigree_to_probdist ped
  let D₁ := S_O_partition layer
  let D₂ := S_D_partition layer

  -- Apply the abstract theorem
  obtain ⟨flow_prob, h_flow⟩ := prob_partition_is_feasible_flow D D₁ D₂ p

  constructor
  · -- Origin conservation: ∑_{e'} f(e,e') = supply(e)
    intro e he

    -- Supply equals probability of S_O(e)
    have h_supply_eq : supply ped layer e = prob_subset p (layer.S_O e) := by
      rfl

    -- Use the abstract theorem's origin conservation property
    have h_origin := flow_prob.h_origin_conservation (layer.S_O e) (by
      show layer.S_O e ∈ (S_O_partition layer).parts
      show layer.S_O e ∈ layer.edges_k.image layer.S_O
      rw [Finset.mem_image]
      exact ⟨e, he, rfl⟩)

    -- Chain of equalities showing pedigree flow satisfies conservation
    calc
      ∑ e' ∈ layer.edges_k1, pedigree_flow ped layer e e'
        = ∑ e' ∈ layer.edges_k1, prob_subset p (layer.S_O e ∩ layer.S_D e') := by
          rfl
      _ = ∑ e' ∈ layer.edges_k1, flow_prob.flow (layer.S_O e) (layer.S_D e') := by
          apply Finset.sum_congr rfl
          intro e' he'
          -- Show our flow matches the abstract flow
          have h_e_in : layer.S_O e ∈ (S_O_partition layer).parts := by
            show layer.S_O e ∈ layer.edges_k.image layer.S_O
            rw [Finset.mem_image]
            exact ⟨e, he, rfl⟩
          have h_e'_in : layer.S_D e' ∈ (S_D_partition layer).parts := by
            show layer.S_D e' ∈ layer.edges_k1.image layer.S_D
            rw [Finset.mem_image]
            exact ⟨e', he', rfl⟩
          have h_eq := h_flow (layer.S_O e) h_e_in (layer.S_D e') h_e'_in
          rw [S_intersection] at h_eq
          exact h_eq.symm
      _ = ∑ s ∈ layer.edges_k1.image layer.S_D, flow_prob.flow (layer.S_O e) s := by
          -- Reindex the sum from edges to partition parts
          rw [Finset.sum_image]
          -- Prove S_D is injective (different edges → different parts)
          intro e₁ he₁ e₂ he₂ heq
          by_contra hne
          have hdisj := layer.h_S_D_disjoint e₁ he₁ e₂ he₂ hne
          rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
          have hnonempty₁ := layer.h_S_D_nonempty e₁ he₁
          rw [← heq] at hdisj
          rw [Finset.inter_self] at hdisj
          rw [hdisj] at hnonempty₁
          exact Finset.not_nonempty_empty hnonempty₁
      _ = ∑ s ∈ D₂.parts, flow_prob.flow (layer.S_O e) s := by
          -- D₂.parts is definitionally equal to the image
          show ∑ s ∈ layer.edges_k1.image layer.S_D, flow_prob.flow (layer.S_O e) s =
               ∑ s ∈ (S_D_partition layer).parts, flow_prob.flow (layer.S_O e) s
          rfl
      _ = prob_subset p (layer.S_O e) := h_origin
      _ = supply ped layer e := h_supply_eq.symm

  constructor
  · -- Sink conservation: ∑_{e} f(e,e') = demand(e')
    intro e' he'

    have h_demand_eq : demand ped layer e' = prob_subset p (layer.S_D e') := by
      rfl

    have h_sink := flow_prob.h_sink_conservation (layer.S_D e') (by
      show layer.S_D e' ∈ (S_D_partition layer).parts
      show layer.S_D e' ∈ layer.edges_k1.image layer.S_D
      rw [Finset.mem_image]
      exact ⟨e', he', rfl⟩)

    -- h_sink gives us: ∑ o ∈ D₁.parts, flow_prob.flow o (layer.S_D e') = prob_subset p (layer.S_D e')
    -- But we need the flow arguments flipped, so we need to work differently

    calc
      ∑ e ∈ layer.edges_k, pedigree_flow ped layer e e'
        = ∑ e ∈ layer.edges_k, prob_subset p (layer.S_O e ∩ layer.S_D e') := by
          rfl
      _ = ∑ e ∈ layer.edges_k, prob_subset p (layer.S_D e' ∩ layer.S_O e) := by
          congr 1
          ext e
          rw [Finset.inter_comm]
      _ = ∑ e ∈ layer.edges_k, ∑ x ∈ (layer.S_D e' ∩ layer.S_O e), p.prob x := by
          rfl
      _ = ∑ e ∈ layer.edges_k, ∑ x ∈ (layer.S_O e ∩ layer.S_D e'), p.prob x := by
          congr 1
          ext e
          rw [Finset.inter_comm]
      _ = ∑ e ∈ layer.edges_k, prob_subset p (layer.S_O e ∩ layer.S_D e') := by
          rfl
      _ = ∑ s ∈ layer.edges_k.image layer.S_O, prob_subset p (s ∩ layer.S_D e') := by
          rw [Finset.sum_image]
          intro e₁ he₁ e₂ he₂ heq
          by_contra hne
          have hdisj := layer.h_S_O_disjoint e₁ he₁ e₂ he₂ hne
          rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
          have hnonempty₁ := layer.h_S_O_nonempty e₁ he₁
          rw [← heq] at hdisj
          rw [Finset.inter_self] at hdisj
          rw [hdisj] at hnonempty₁
          exact Finset.not_nonempty_empty hnonempty₁
      _ = ∑ s ∈ D₁.parts, prob_subset p (s ∩ layer.S_D e') := by
          show ∑ s ∈ layer.edges_k.image layer.S_O, prob_subset p (s ∩ layer.S_D e') =
               ∑ s ∈ (S_O_partition layer).parts, prob_subset p (s ∩ layer.S_D e')
          rfl
      _ = prob_subset p (layer.S_D e') := by
          -- This follows from the partition property
          conv_lhs =>
            arg 2
            ext s
            rw [Finset.inter_comm]
          exact (prob_origin_equals_sum_intersections ped.pedigrees D₂ D₁ p (layer.S_D e') (by
            show layer.S_D e' ∈ layer.edges_k1.image layer.S_D
            rw [Finset.mem_image]
            exact ⟨e', he', rfl⟩)).symm
      _ = demand ped layer e' := h_demand_eq.symm

  constructor
  · -- Non-negativity: f(e,e') ≥ 0
    intro e he e' he'
    unfold pedigree_flow
    apply Finset.sum_nonneg
    intro r hr
    exact ped.h_nonneg r (layer.h_S_O_subsets e he (Finset.mem_of_mem_inter_left hr))

  · -- Arc structure: empty intersection → zero flow
    intro e he e' he' hempty
    unfold pedigree_flow
    simp [hempty]

/-!
## Conclusion

This proof demonstrates that:

1. **Abstraction pays off**: The pedigree bipartite flow problem is a special case
   of the partition probability flow problem

2. **All flow properties follow from the abstract theorem**:
   - Origin conservation (outflow = supply)
   - Sink conservation (inflow = demand)
   - Non-negativity
   - Arc structure

3. **Deep mathematical structure**: The feasibility of pedigree polytopes is
   fundamentally about probability distributions over partition refinements

4. **Reusable proof technique**: This pattern applies to any flow problem
   where arcs connect partition refinements

## Key Proof Techniques Used

- **Structure conversion**: Mapping domain-specific structures to abstract ones
- **Definitional equality**: Using `rfl` when definitions match exactly
- **Sum reindexing**: Using `Finset.sum_image` to change index sets
- **Injectivity via partition properties**: Proving injectivity using disjointness
- **Calc chains**: Building equational proofs step-by-step
-/
