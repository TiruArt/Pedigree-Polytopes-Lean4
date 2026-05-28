import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import MembershipProject.Core.PartitionProbabilityFlowProblem

/-!
# Teaching Version: Pedigree Polytope Bipartite Flow

## Learning Objectives

After studying this file, you should understand:
1. How to translate domain-specific problems into abstract mathematical structures
2. How to apply general theorems to specific instances
3. Key Lean 4 proof techniques: pattern matching, calc chains, sum reindexing
4. How to prove properties using partition structure

## Prerequisites

- Basic Lean 4 syntax and tactics
- Understanding of finsets and sums
- Familiarity with partition concepts
- The PartitionProbabilityFlowProblem module

## The Big Picture

**Problem**: Prove that a certain flow on a bipartite graph is feasible

**Solution Strategy**:
1. Recognize this as an instance of an abstract pattern
2. Convert our specific structures to the abstract form
3. Apply the general theorem
4. Extract the specific conclusions we need

This is a fundamental pattern in mathematics: prove once generally, apply many times.
-/

open Finset BigOperators

/-! ### Part 1: Domain-Specific Structures

We start by defining the structures specific to our pedigree problem.
These capture the biological/genealogical concepts.
-/

/-
  **LEARNING NOTE**: Structure definitions in Lean 4

  A `structure` bundles data with constraints. Here:
  - `pedigrees`: the actual data (a finite set)
  - `weights`: a function assigning weights
  - `h_nonneg`, `h_sum_one`, `h_support`: constraints that must hold

  The `where` keyword introduces the fields.
-/
structure PedigreeStructure (R : Type*) [DecidableEq R] [Fintype R] (n : ℕ) where
  pedigrees : Finset R
  weights : R → ℝ
  h_nonneg : ∀ r ∈ pedigrees, 0 ≤ weights r
  h_sum_one : ∑ r ∈ pedigrees, weights r = 1
  h_support : ∀ r ∉ pedigrees, weights r = 0

/-
  **LEARNING NOTE**: Type parameters

  - `R : Type*` means R can be any type
  - `[DecidableEq R]` means we can decide if two R's are equal
  - `[Fintype R]` means R has finitely many elements
  - `(n : ℕ)` is just a natural number parameter

  These are like "generic" types in other languages, but with extra constraints.
-/

structure Edge (k : ℕ) where
  node1 : ℕ
  node2 : ℕ
  h_layer : node1 < node2

/-
  **LEARNING NOTE**: Partition properties

  A partition of a set S is a collection of:
  - Non-empty subsets
  - That are pairwise disjoint
  - That cover all of S

  We encode these as four properties: nonempty, disjoint, covers, subsets
-/
structure LayerStructure (R : Type*) [DecidableEq R] [Fintype R]
    (n k : ℕ) (ped : PedigreeStructure R n) where
  edges_k : Finset (Edge k)
  edges_k1 : Finset (Edge (k+1))
  S_O : Edge k → Finset R
  S_D : Edge (k+1) → Finset R
  -- Partition axioms for S_O
  h_S_O_nonempty : ∀ e ∈ edges_k, (S_O e).Nonempty
  h_S_O_disjoint : ∀ e₁ ∈ edges_k, ∀ e₂ ∈ edges_k, e₁ ≠ e₂ → Disjoint (S_O e₁) (S_O e₂)
  h_S_O_covers : ∀ r ∈ ped.pedigrees, ∃ e ∈ edges_k, r ∈ S_O e
  h_S_O_subsets : ∀ e ∈ edges_k, S_O e ⊆ ped.pedigrees
  -- Partition axioms for S_D
  h_S_D_nonempty : ∀ e ∈ edges_k1, (S_D e).Nonempty
  h_S_D_disjoint : ∀ e₁ ∈ edges_k1, ∀ e₂ ∈ edges_k1, e₁ ≠ e₂ → Disjoint (S_D e₁) (S_D e₂)
  h_S_D_covers : ∀ r ∈ ped.pedigrees, ∃ e ∈ edges_k1, r ∈ S_D e
  h_S_D_subsets : ∀ e ∈ edges_k1, S_D e ⊆ ped.pedigrees

/-
  **LEARNING NOTE**: Variable declarations

  This `variable` declaration makes R implicit in all following definitions.
  Instead of writing `{R : Type*} [DecidableEq R] [Fintype R]` every time,
  Lean automatically adds these parameters where needed.
-/
variable {R : Type*} [DecidableEq R] [Fintype R]

/-! ### Part 2: Translation to Abstract Structures

Now we translate our domain-specific structures to the abstract
partition probability structures.
-/

/-
  **LEARNING NOTE**: Definition as structure instance

  This creates a `ProbDist` (probability distribution) from our pedigree weights.
  The `where` clauses fill in the required fields of ProbDist.

  Notice: we just pass along the existing proofs!
-/
def pedigree_to_probdist {n : ℕ} (ped : PedigreeStructure R n) :
    ProbDist ped.pedigrees where
  prob := ped.weights
  h_nonneg := ped.h_nonneg
  h_sum_one := ped.h_sum_one
  h_support := ped.h_support

/-
  **LEARNING NOTE**: Image of a function

  `layer.edges_k.image layer.S_O` means:
  "Apply S_O to every edge in edges_k, collect the results"

  Mathematically: {S_O(e) | e ∈ edges_k}
-/
def S_O_partition {n k : ℕ} {ped : PedigreeStructure R n}
    (layer : LayerStructure R n k ped) :
    FinsetPartition ped.pedigrees where
  parts := layer.edges_k.image layer.S_O

  /-
    **LEARNING NOTE**: Pattern matching in proofs

    `match hs with | ⟨e, he, heq⟩ => ...` destructures the proof
    that s ∈ image S_O into:
    - e: an edge
    - he: proof that e ∈ edges_k
    - heq: proof that S_O e = s
  -/
  h_nonempty := by
    intro s hs
    rw [Finset.mem_image] at hs
    match hs with
    | ⟨e, he, heq⟩ =>
      rw [← heq]  -- Rewrite goal using the equality
      exact layer.h_S_O_nonempty e he

  /-
    **LEARNING NOTE**: Proof by contradiction

    `by_contra hne` assumes the negation and derives a contradiction.
    Here: assume e₁ ≠ e₂, then s₁ and s₂ are disjoint,
    but they're equal, so their intersection with themselves is empty,
    contradicting non-emptiness.
  -/
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

  /-
    **LEARNING NOTE**: Obtain and use

    `obtain ⟨e, he, hr_in⟩ := ...` destructures an existence proof.
    `use x` provides x as the witness for an existence goal.
  -/
  h_covers := by
    intro r hr
    obtain ⟨e, he, hr_in⟩ := layer.h_S_O_covers r hr
    use layer.S_O e
    constructor
    · rw [Finset.mem_image]
      exact ⟨e, he, rfl⟩  -- rfl proves S_O e = S_O e
    · exact hr_in

  h_subsets := by
    intro s hs
    rw [Finset.mem_image] at hs
    match hs with
    | ⟨e, he, heq⟩ =>
      rw [← heq]
      exact layer.h_S_O_subsets e he

/- **LEARNING NOTE**: Same structure, different data

   S_D_partition is almost identical to S_O_partition,
   just using S_D instead of S_O. This repetition could be
   abstracted further, but keeping it explicit aids understanding.
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

/-! ### Part 3: Flow Definitions

These define supply, demand, and flow in our pedigree context.
-/

/-
  **LEARNING NOTE**: Definitional equality

  These are "def" not "theorem" because they're computational.
  Lean can evaluate supply/demand/flow on concrete inputs.
-/
def supply {n k : ℕ} (ped : PedigreeStructure R n)
    (layer : LayerStructure R n k ped) (e : Edge k) : ℝ :=
  ∑ r ∈ layer.S_O e, ped.weights r

def demand {n k : ℕ} (ped : PedigreeStructure R n)
    (layer : LayerStructure R n k ped) (e' : Edge (k+1)) : ℝ :=
  ∑ r ∈ layer.S_D e', ped.weights r

/-
  **KEY DEFINITION**: The flow formula

  Flow on arc (e, e') = sum of weights of pedigrees in BOTH S_O(e) AND S_D(e')

  This is exactly f(o, s) = p(o ∩ s) from the abstract theorem!
-/
def pedigree_flow {n k : ℕ} (ped : PedigreeStructure R n)
    (layer : LayerStructure R n k ped)
    (e : Edge k) (e' : Edge (k+1)) : ℝ :=
  ∑ r ∈ (layer.S_O e ∩ layer.S_D e'), ped.weights r

/-! ### Part 4: The Main Theorem

Now we prove feasibility by applying the abstract theorem.
-/

/-
  **LEARNING NOTE**: Theorem statement structure

  The theorem states four properties connected by ∧ (and):
  1. Origin conservation
  2. Sink conservation
  3. Non-negativity
  4. Arc structure

  We'll prove each with `constructor` to split the conjunction.
-/
theorem pedigree_bipartite_flow_feasible
    {n k : ℕ}
    (ped : PedigreeStructure R n)
    (layer : LayerStructure R n k ped) :
    (∀ e ∈ layer.edges_k,
      ∑ e' ∈ layer.edges_k1, pedigree_flow ped layer e e' =
      supply ped layer e) ∧
    (∀ e' ∈ layer.edges_k1,
      ∑ e ∈ layer.edges_k, pedigree_flow ped layer e e' =
      demand ped layer e') ∧
    (∀ e ∈ layer.edges_k, ∀ e' ∈ layer.edges_k1,
      0 ≤ pedigree_flow ped layer e e') ∧
    (∀ e ∈ layer.edges_k, ∀ e' ∈ layer.edges_k1,
      layer.S_O e ∩ layer.S_D e' = ∅ → pedigree_flow ped layer e e' = 0) := by

  /-
    **LEARNING NOTE**: Let bindings in proofs

    `let D := ...` creates local definitions.
    These are just abbreviations - they don't change the goal,
    but make the proof more readable.
  -/
  let D := ped.pedigrees
  let p := pedigree_to_probdist ped
  let D₁ := S_O_partition layer
  let D₂ := S_D_partition layer

  /-
    **THE KEY STEP**: Apply the abstract theorem!

    `obtain ⟨flow_prob, h_flow⟩ := ...` gets us:
    - flow_prob: a FlowProblem instance
    - h_flow: proof that flow values match our formula

    This single line gives us feasibility for free!
  -/
  obtain ⟨flow_prob, h_flow⟩ := prob_partition_is_feasible_flow D D₁ D₂ p

  /-
    **LEARNING NOTE**: Constructor tactic

    `constructor` splits an `∧` goal into two subgoals.
    We use it three times to split our four-way conjunction.
  -/
  constructor
  · -- Proof of origin conservation
    intro e he

    /-
      **LEARNING NOTE**: rfl for definitional equality

      `rfl` (reflexivity) proves X = X.
      Here it works because supply and prob_subset are
      definitionally equal given our definitions.
    -/
    have h_supply_eq : supply ped layer e = prob_subset p (layer.S_O e) := by
      rfl

    /-
      **LEARNING NOTE**: Show tactic

      `show P` changes the goal to P (if they're definitionally equal).
      This helps Lean and the reader understand what we're proving.
    -/
    have h_origin := flow_prob.h_origin_conservation (layer.S_O e) (by
      show layer.S_O e ∈ (S_O_partition layer).parts
      show layer.S_O e ∈ layer.edges_k.image layer.S_O
      rw [Finset.mem_image]
      exact ⟨e, he, rfl⟩)

    /-
      **LEARNING NOTE**: Calc chains

      `calc` creates a chain of equalities:
        A = B := proof_1
      _ = C := proof_2
      _ = D := proof_3

      Lean automatically chains them: A = B = C = D, so A = D.
      This is perfect for step-by-step mathematical reasoning!
    -/
    calc
      ∑ e' ∈ layer.edges_k1, pedigree_flow ped layer e e'
        = ∑ e' ∈ layer.edges_k1, prob_subset p (layer.S_O e ∩ layer.S_D e') := by
          rfl  -- Definitionally equal
      _ = ∑ e' ∈ layer.edges_k1, flow_prob.flow (layer.S_O e) (layer.S_D e') := by
          /-
            **LEARNING NOTE**: Finset.sum_congr

            To prove two sums are equal:
            - First prove the index sets are equal (here: rfl)
            - Then prove each term is equal

            Using `sum_congr` instead of `congr; ext` is important
            because it gives us the membership proof `he'` in the context.
          -/
          apply Finset.sum_congr rfl
          intro e' he'  -- Now we have he' : e' ∈ layer.edges_k1
          -- Prove membership in partition parts
          have h_e_in : layer.S_O e ∈ (S_O_partition layer).parts := by
            show layer.S_O e ∈ layer.edges_k.image layer.S_O
            rw [Finset.mem_image]
            exact ⟨e, he, rfl⟩
          have h_e'_in : layer.S_D e' ∈ (S_D_partition layer).parts := by
            show layer.S_D e' ∈ layer.edges_k1.image layer.S_D
            rw [Finset.mem_image]
            exact ⟨e', he', rfl⟩  -- Use the he' from sum_congr!
          have h_eq := h_flow (layer.S_O e) h_e_in (layer.S_D e') h_e'_in
          rw [S_intersection] at h_eq
          exact h_eq.symm
      _ = ∑ s ∈ layer.edges_k1.image layer.S_D, flow_prob.flow (layer.S_O e) s := by
          /-
            **LEARNING NOTE**: Sum reindexing with Finset.sum_image

            If we have ∑ x ∈ S, f(g(x)) and g is injective,
            then ∑ x ∈ S, f(g(x)) = ∑ y ∈ image(g, S), f(y)

            We need to prove injectivity: g(x₁) = g(x₂) → x₁ = x₂
          -/
          rw [Finset.sum_image]
          intro e₁ he₁ e₂ he₂ heq  -- Assume S_D e₁ = S_D e₂
          by_contra hne            -- Assume e₁ ≠ e₂ for contradiction
          -- If e₁ ≠ e₂, their S_D parts are disjoint
          have hdisj := layer.h_S_D_disjoint e₁ he₁ e₂ he₂ hne
          rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
          -- But they're equal, so intersection with self is empty?
          have hnonempty₁ := layer.h_S_D_nonempty e₁ he₁
          rw [← heq] at hdisj
          rw [Finset.inter_self] at hdisj
          -- This contradicts non-emptiness!
          rw [hdisj] at hnonempty₁
          exact Finset.not_nonempty_empty hnonempty₁
      _ = ∑ s ∈ D₂.parts, flow_prob.flow (layer.S_O e) s := by
          show ∑ s ∈ layer.edges_k1.image layer.S_D, flow_prob.flow (layer.S_O e) s =
               ∑ s ∈ (S_D_partition layer).parts, flow_prob.flow (layer.S_O e) s
          rfl  -- D₂.parts is definitionally the image
      _ = prob_subset p (layer.S_O e) := h_origin  -- From abstract theorem!
      _ = supply ped layer e := h_supply_eq.symm

  constructor
  · -- Proof of sink conservation
    /-
      **LEARNING NOTE**: Symmetric argument

      The sink conservation proof has the same structure as origin conservation,
      but with the roles of D₁ and D₂ reversed.

      The key insight: we can't directly use h_sink from the abstract theorem
      because the flow arguments are in different order. Instead, we:
      1. Stay in prob_subset notation throughout
      2. Use sum reindexing to change from edges to partition parts
      3. Apply the partition lemma (prob_origin_equals_sum_intersections)
         with D₁ and D₂ swapped
    -/
    intro e' he'

    have h_demand_eq : demand ped layer e' = prob_subset p (layer.S_D e') := by
      rfl

    calc
      ∑ e ∈ layer.edges_k, pedigree_flow ped layer e e'
        = ∑ e ∈ layer.edges_k, prob_subset p (layer.S_O e ∩ layer.S_D e') := by
          rfl
      _ = ∑ e ∈ layer.edges_k, prob_subset p (layer.S_D e' ∩ layer.S_O e) := by
          /-
            **LEARNING NOTE**: Rewriting inside sums

            When we need to rewrite inside every term of a sum,
            we use `congr 1; ext` to focus on a single term.
          -/
          congr 1
          ext e
          rw [Finset.inter_comm]  -- Intersection is commutative
      _ = ∑ e ∈ layer.edges_k, ∑ x ∈ (layer.S_D e' ∩ layer.S_O e), p.prob x := by
          rfl
      _ = ∑ e ∈ layer.edges_k, ∑ x ∈ (layer.S_O e ∩ layer.S_D e'), p.prob x := by
          congr 1
          ext e
          rw [Finset.inter_comm]
      _ = ∑ e ∈ layer.edges_k, prob_subset p (layer.S_O e ∩ layer.S_D e') := by
          rfl
      _ = ∑ s ∈ layer.edges_k.image layer.S_O, prob_subset p (s ∩ layer.S_D e') := by
          -- Same reindexing as before, proving S_O is injective
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
          /-
            **LEARNING NOTE**: Using helper lemmas

            We apply `prob_origin_equals_sum_intersections` which says:
            For a partition D₁, ∑_{s ∈ D₁} p(s ∩ t) = p(t)

            The `conv_lhs` tactic lets us rewrite inside specific parts
            of the goal. Here we flip the intersection order.
          -/
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
  · -- Proof of non-negativity (direct from probability non-negativity)
    intro e he e' he'
    unfold pedigree_flow
    /-
      **LEARNING NOTE**: Sum non-negativity

      If every term is ≥ 0, then the sum is ≥ 0.
      This is `Finset.sum_nonneg` from Mathlib.
    -/
    apply Finset.sum_nonneg
    intro r hr
    -- Each weight is non-negative (from ProbDist property)
    exact ped.h_nonneg r (layer.h_S_O_subsets e he (Finset.mem_of_mem_inter_left hr))

  · -- Proof of arc structure (empty intersection → zero sum)
    intro e he e' he' hempty
    unfold pedigree_flow
    simp [hempty]  -- Sum over empty set is 0

/-! ## Summary of Key Techniques

### 1. Structure Translation
Convert domain-specific structures to abstract mathematical structures by:
- Identifying the correspondence (pedigrees ↔ probability domain)
- Creating conversion functions (pedigree_to_probdist, S_O_partition, S_D_partition)
- Proving the conversion preserves all required properties

### 2. Definitional Equality
Use `rfl` when definitions are definitionally equal:
```lean
have h : supply ped layer e = prob_subset p (layer.S_O e) := by rfl
```

### 3. Pattern Matching
Destructure existence proofs:
```lean
match hs with
| ⟨e, he, heq⟩ => ...
```

### 4. Calc Chains
Build step-by-step equational proofs for clarity:
```lean
calc A = B := proof1
   _ = C := proof2
   _ = D := proof3
```

### 5. Sum Reindexing
Change the index set of a sum using `Finset.sum_image`:
```lean
∑ x ∈ S, f(g(x)) = ∑ y ∈ image(g, S), f(y)
```
Requires proving g is injective (different inputs → different outputs)

### 6. Injectivity via Partitions
Prove injectivity using partition properties:
- If g(x₁) = g(x₂) but x₁ ≠ x₂
- Then the parts are disjoint (partition property)
- But they're equal, so their intersection with themselves is empty
- But they're non-empty (partition property)
- Contradiction!

### 7. Sum Congruence
When proving sums are equal, use `Finset.sum_congr`:
```lean
apply Finset.sum_congr rfl  -- Index sets equal
intro x hx                   -- Prove each term equal, with hx available
```
This is better than `congr; ext` because it gives you the membership proof.

### 8. Rewriting Inside Terms
Use `conv_lhs` to rewrite in specific locations:
```lean
conv_lhs =>
  arg 2      -- Focus on second argument
  ext x      -- For each x
  rw [...]   -- Apply rewrite
```

### 9. Helper Lemmas
Factor out common patterns into reusable lemmas:
- `prob_origin_equals_sum_intersections`: partition property for probabilities
- `intersections_pairwise_disjoint`: intersection preservation of disjointness
- These make main proofs cleaner and more understandable

## Common Pitfalls and Solutions

### Pitfall 1: Missing membership proofs
**Problem**: `ext e'` doesn't give you `e' ∈ S`
**Solution**: Use `sum_congr rfl; intro e' he'` instead

### Pitfall 2: Wrong direction equality
**Problem**: Have `h : A = B` but need `B = A`
**Solution**: Use `h.symm`

-/
