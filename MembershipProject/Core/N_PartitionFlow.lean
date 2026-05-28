-- File No. 5 - N_PartitionFlow.lean
--
-- Partition Probability Flow Theorem (Lemma 3, arXiv:2507.09069v1).
--
-- STATEMENT:
--   Given a finite set D, two partitions D₁ and D₂ of D,
--   and a probability distribution p over D,
--   the flow f(o,s) = p(o ∩ s) for o ∈ D₁, s ∈ D₂
--   is a feasible solution to the corresponding flow problem.
--
-- PROOF OUTLINE:
--   1. Origin conservation: Σ_s p(o ∩ s) = p(o)
--      since {o ∩ s | s ∈ D₂} partitions o (D₂ covers D, o ⊆ D).
--   2. Sink conservation: Σ_o p(o ∩ s) = p(s)
--      by symmetry of intersection: o ∩ s = s ∩ o.
--   3. Non-negativity: p(o ∩ s) ≥ 0 from p ≥ 0.
--   4. Arc existence: o ∩ s = ∅ → f(o,s) = 0 (empty sum).
--
-- Reference: Arthanari, T.S. arXiv:2507.09069v1 [math.CO].

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators Set

variable {α : Type*} [DecidableEq α] [Fintype α]

-- ============================================================
-- PROBABILITY DISTRIBUTION
-- A probability distribution over a finite set D:
-- non-negative weights summing to 1, zero outside D.
-- ============================================================

structure ProbDist (D : Finset α) where
  prob      : α → ℝ
  h_nonneg  : ∀ x ∈ D, 0 ≤ prob x
  h_sum_one : ∑ x ∈ D, prob x = 1
  h_support : ∀ x ∉ D, prob x = 0

-- ============================================================
-- FINSET PARTITION
-- A partition of D: non-empty, pairwise disjoint parts covering D.
-- ============================================================

structure FinsetPartition (D : Finset α) where
  parts      : Finset (Finset α)
  h_nonempty : ∀ s ∈ parts, s.Nonempty
  h_disjoint : ∀ s₁ ∈ parts, ∀ s₂ ∈ parts, s₁ ≠ s₂ → Disjoint s₁ s₂
  h_covers   : ∀ x ∈ D, ∃ s ∈ parts, x ∈ s
  h_subsets  : ∀ s ∈ parts, s ⊆ D

-- ============================================================
-- FLOW PROBLEM
-- Origins: parts of D₁. Sinks: parts of D₂.
-- f(o,s) = flow on arc (o,s).
-- Supply at o = p(o). Demand at s = p(s).
-- ============================================================

structure FlowProblem (D : Finset α) (D₁ D₂ : FinsetPartition D)
    (p : ProbDist D) where
  flow : Finset α → Finset α → ℝ
  h_origin_conservation : ∀ o ∈ D₁.parts,
    ∑ s ∈ D₂.parts, flow o s = ∑ x ∈ o, p.prob x
  h_sink_conservation : ∀ s ∈ D₂.parts,
    ∑ o ∈ D₁.parts, flow o s = ∑ x ∈ s, p.prob x
  h_nonneg    : ∀ o ∈ D₁.parts, ∀ s ∈ D₂.parts, 0 ≤ flow o s
  h_arc_exists : ∀ o ∈ D₁.parts, ∀ s ∈ D₂.parts,
    o ∩ s = ∅ → flow o s = 0

-- ============================================================
-- DEFINITIONS
-- ============================================================

/-- S_{o,s} = o ∩ s: the set of elements in both o and s. -/
def S_intersection (o s : Finset α) : Finset α := o ∩ s

/-- p(S) = Σ_{x ∈ S} p(x): probability of a subset. -/
def prob_subset {D : Finset α} (p : ProbDist D) (S : Finset α) : ℝ :=
  ∑ x ∈ S, p.prob x

-- ============================================================
-- HELPER LEMMAS
-- ============================================================

/-- Each part o of D₁ equals the disjoint union of its intersections
    with the parts of D₂, since D₂ covers D and o ⊆ D. -/
lemma partition_union_intersections
    (D : Finset α) (D₁ D₂ : FinsetPartition D)
    (o : Finset α) (h_o : o ∈ D₁.parts) :
    o = Finset.biUnion D₂.parts (fun s => o ∩ s) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_inter]
  constructor
  · intro hx
    have hx_in_D : x ∈ D := D₁.h_subsets o h_o hx
    obtain ⟨s, hs_mem, hx_in_s⟩ := D₂.h_covers x hx_in_D
    exact ⟨s, hs_mem, hx, hx_in_s⟩
  · rintro ⟨s, _, hxo, _⟩
    exact hxo

/-- The intersections {o ∩ s | s ∈ D₂} are pairwise disjoint
    (since the parts of D₂ are pairwise disjoint). -/
lemma intersections_pairwise_disjoint
    (D : Finset α) (D₁ D₂ : FinsetPartition D)
    (o : Finset α) (h_o : o ∈ D₁.parts) :
    ∀ s₁ ∈ D₂.parts, ∀ s₂ ∈ D₂.parts,
      s₁ ≠ s₂ → Disjoint (o ∩ s₁) (o ∩ s₂) := by
  intro s₁ hs₁ s₂ hs₂ hne
  exact Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right
      (D₂.h_disjoint s₁ hs₁ s₂ hs₂ hne))

/-- p(o) = Σ_s p(o ∩ s): probability of a part equals sum over intersections. -/
lemma prob_origin_equals_sum_intersections
    (D : Finset α) (D₁ D₂ : FinsetPartition D) (p : ProbDist D)
    (o : Finset α) (h_o : o ∈ D₁.parts) :
    ∑ x ∈ o, p.prob x = ∑ s ∈ D₂.parts, prob_subset p (o ∩ s) := by
  unfold prob_subset
  conv_lhs => rw [partition_union_intersections D D₁ D₂ o h_o]
  rw [Finset.sum_biUnion (intersections_pairwise_disjoint D D₁ D₂ o h_o)]

-- ============================================================
-- MAIN THEOREM: f(o,s) = p(o ∩ s) is a feasible flow
-- ============================================================

/-- Partition Probability Flow Theorem (arXiv:2507.09069v1, Lemma 3):
    The flow f(o,s) = p(o ∩ s) satisfies all flow problem constraints.
    This establishes the connection between partition refinements,
    probability distributions, and feasible flows in bipartite networks. -/
theorem prob_partition_is_feasible_flow
    (D : Finset α) (D₁ D₂ : FinsetPartition D) (p : ProbDist D) :
    ∃ (f : FlowProblem D D₁ D₂ p),
      ∀ o ∈ D₁.parts, ∀ s ∈ D₂.parts,
        f.flow o s = prob_subset p (S_intersection o s) := by
  let flow_fn := fun o s => prob_subset p (S_intersection o s)
  exact ⟨{
    flow := flow_fn
    h_origin_conservation := fun o ho => by
      unfold flow_fn S_intersection
      exact (prob_origin_equals_sum_intersections D D₁ D₂ p o ho).symm
    h_sink_conservation := fun s hs => by
      unfold flow_fn S_intersection
      conv_lhs =>
        arg 2; ext o; rw [Finset.inter_comm o s]
      exact (prob_origin_equals_sum_intersections D D₂ D₁ p s hs).symm
    h_nonneg := fun o ho s hs => by
      unfold flow_fn prob_subset
      apply Finset.sum_nonneg
      intro x hx
      exact p.h_nonneg x (D₁.h_subsets o ho (Finset.mem_of_mem_inter_left hx))
    h_arc_exists := fun o _ s _ hempty => by
      unfold flow_fn prob_subset S_intersection
      simp [hempty]
  }, fun _ _ _ _ => rfl⟩
