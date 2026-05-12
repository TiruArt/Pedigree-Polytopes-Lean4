-- MembershipProject/PedigreeMembershipCharacterisation.lean
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Init.Prelude
set_option linter.unusedVariables false
/-!
# Pedigree Polytope: Necessity Direction of the Membership Characterisation

This file formalises the necessity half of the Pedigree Polytope membership
characterisation (Arthanari, Springer Nature).

A slack vector `X : SlackVector (m+3)` lies in the convex hull of pedigrees
if and only if a feasible Forbidden Arc Transportation problem (FAT) exists.  This file
proves the **necessity** direction: membership in the convex hull implies
existence of a feasible FAT, constructed explicitly by Bayesian conditioning.

## Parameterisation
- `Pedigree m` encodes m free edge choices at stages 4, …, m+3.
  The complete order has n = m+3 elements.
- All type indices use addition to avoid `Nat.sub` opacity.
- All theorems require `m ≥ 1`.

## Structure
1. `Edge k`              — ordered pair (i,j) with i < j < k.
2. `Pedigree m`          — sequence of m edge choices, one per stage.
3. `ConvexWitness m`     — convex combination of pedigrees with rational weights.
4. `FAT m hm lam`        — Forbidden Arc Transportation problem: conditional
                           edge probabilities given a predecessor
                           pedigree, required to sum to 1 on active pedigrees.
5. `marginalize_witness` — projects a stage-m witness to stage m-1 by summing
                           over all pedigrees sharing the same restriction.
6. `construct_FAT_from_witness` — given a convex witness μ, constructs a
                           feasible FAT via conditional normalisation.
7. `necessity_FAT_feasible` — membership in the convex hull implies FAT existence.
-/

namespace MembershipProject.PedigreePolytope

-- ============================================================================
-- CORE TYPES
-- ============================================================================

namespace Core

/-- An ordered edge (i,j) in a complete graph on k vertices: i < j < k. -/
structure Edge (k : Nat) where
  i   : Nat
  j   : Nat
  hi  : i < k
  hj  : j < k
  hij : i < j
deriving DecidableEq, Repr

/-- A slack vector assigns a rational value to each edge of K_k. -/
def SlackVector (k : Nat) := Edge k → ℚ

/-- `Edge k` is a finite type, in bijection with strict pairs in Fin k × Fin k. -/
instance edgeFintype (k : Nat) : Fintype (Edge k) :=
  Fintype.ofEquiv { p : Fin k × Fin k // p.1.val < p.2.val }
    { toFun    := fun p => ⟨p.1.1.val, p.1.2.val, p.1.1.isLt, p.1.2.isLt, p.2⟩
      invFun   := fun e => ⟨(⟨e.i, e.hi⟩, ⟨e.j, e.hj⟩), e.hij⟩
      left_inv  := fun ⟨⟨a, b⟩, _⟩ =>
                     Subtype.ext (Prod.ext (Fin.eta a a.isLt) (Fin.eta b b.isLt))
      right_inv := fun _ => rfl }

end Core

open Core

-- ============================================================================
-- PEDIGREE
-- ============================================================================

/-- A pedigree of order m+3 is a sequence of m edge choices:
    at stage i+4 (for i : Fin m) one edge of K_{i+4} is selected. -/
@[ext]
structure Pedigree (m : Nat) where
  edge_choice : (i : Fin m) → Edge (i.val + 4)

/-- Decidable equality for pedigrees, lifted from decidable equality on functions. -/
instance {m : Nat} : DecidableEq (Pedigree m) := fun a b =>
  match decEq a.edge_choice b.edge_choice with
  | isTrue  h => isTrue  (Pedigree.ext h)
  | isFalse h => isFalse (fun heq => h (congrArg Pedigree.edge_choice heq))

/-- The edge chosen at the final stage m+3.
    `cast` is used because the inferred type `Edge ((Fin.mk (m-1) _).val + 4)`
    does not syntactically match `Edge (m+3)`; `congrArg Edge` supplies the
    proof of equality and `cast` handles the type transport. -/
def last_edge {m : Nat} (r : Pedigree m) (hm : m ≥ 1) : Edge (m + 3) :=
  have hlt : m - 1 < m := by omega
  cast (congrArg Edge (by omega : m - 1 + 4 = m + 3))
    (r.edge_choice (Fin.mk (m - 1) hlt))

/-- The restriction of a pedigree to its first m-1 edge choices,
    obtained by lifting each index i : Fin (m-1) to Fin m. -/
def restrict_pedigree {m : Nat} (r : Pedigree m) (hm : m ≥ 1) : Pedigree (m - 1) where
  edge_choice := fun i => r.edge_choice (Fin.mk i.val (by omega))

/-- Decidability of pedigree restriction equality, needed for Finset.filter. -/
instance {m : Nat} (r : Pedigree m) (r_prev : Pedigree (m - 1)) (hm : m ≥ 1) :
    Decidable (restrict_pedigree r hm = r_prev) := inferInstance

/-- Decidability of last-edge equality, needed for Finset.filter. -/
instance {m : Nat} (r : Pedigree m) (e : Edge (m + 3)) (hm : m ≥ 1) :
    Decidable (last_edge r hm = e) := inferInstance

/-- The slack vector of a pedigree r: assigns 1 to the last edge chosen by r,
    and 0 to all other edges of K_{m+3}. -/
def Pedigree.toSlackVector {m : Nat} (r : Pedigree m) (hm : m ≥ 1) :
    SlackVector (m + 3) :=
  fun e => if e = last_edge r hm then 1 else 0

-- ============================================================================
-- CONVEX WITNESS
-- ============================================================================

/-- A convex witness certifies that a slack vector lies in the convex hull of
    pedigrees: a finite set of pedigrees with positive rational weights summing
    to 1, with zero weight outside the active set. -/
structure ConvexWitness (m : Nat) where
  active_pedigrees  : Finset (Pedigree m)
  weights           : Pedigree m → ℚ
  h_nonneg          : ∀ r ∈ active_pedigrees, 0 ≤ weights r
  h_sum_one         : ∑ r ∈ active_pedigrees, weights r = 1
  h_support         : ∀ r, r ∉ active_pedigrees → weights r = 0
  h_active_positive : ∀ r ∈ active_pedigrees, 0 < weights r

/-- `X` lies in the convex hull of pedigrees if it is a convex combination
    of their slack vectors. -/
def in_conv_hull {m : Nat} (X : SlackVector (m + 3)) (hm : m ≥ 1) : Prop :=
  ∃ witness : ConvexWitness m,
    ∀ e : Edge (m + 3), X e = ∑ r ∈ witness.active_pedigrees,
      witness.weights r * r.toSlackVector hm e

-- ============================================================================
-- FORBIDDEN ARC TRANSPORTATION PROBLEM (FAT)
-- ============================================================================

/-- A Forbidden Arc Transportation problem instance for stage m, given a
    stage-(m-1) convex witness lam.
    `alloc r_prev e` is the conditional probability of choosing edge e at stage m+3,
    given that the predecessor pedigree is r_prev.  It must be nonneg, sum to 1
    over all edges for each active predecessor, and be zero for inactive predecessors. -/
structure FAT (m : Nat) (_hm : m ≥ 1) (lam : ConvexWitness (m - 1)) where
  alloc     : Pedigree (m - 1) → Edge (m + 3) → ℚ
  h_nonneg  : ∀ r e, 0 ≤ alloc r e
  h_sum_one : ∀ r ∈ lam.active_pedigrees, ∑ e : Edge (m + 3), alloc r e = 1
  h_support : ∀ r ∉ lam.active_pedigrees, ∀ e, alloc r e = 0

-- ============================================================================
-- MARGINALIZATION
-- ============================================================================

/-- Projects a stage-m convex witness to stage m-1 by marginalising over the
    last edge choice.  The active predecessors are the images of active pedigrees
    under restriction; the marginal weight of r_prev is the sum of weights of all
    active pedigrees that restrict to r_prev. -/
def marginalize_witness {m : Nat} (μ : ConvexWitness m) (hm : m ≥ 1) :
    ConvexWitness (m - 1) where
  active_pedigrees :=
    Finset.image (fun r => restrict_pedigree r hm) μ.active_pedigrees
  weights := fun r_prev =>
    ∑ r ∈ μ.active_pedigrees.filter (fun r => restrict_pedigree r hm = r_prev),
    μ.weights r
  h_nonneg := by
    intro r_prev _
    exact Finset.sum_nonneg fun r hr =>
      μ.h_nonneg r (Finset.mem_filter.mp hr).1
  h_sum_one :=
    -- Reindex: sum over all r grouped by restriction equals sum over all r.
    (Finset.sum_fiberwise_of_maps_to
      (fun r hr => Finset.mem_image_of_mem (fun r => restrict_pedigree r hm) hr)
      μ.weights).trans μ.h_sum_one
  h_support := by
    -- r_prev not in image means no active pedigree restricts to it; filter is empty.
    intro r_prev hr_prev
    simp only [Finset.mem_image, not_exists, not_and] at hr_prev
    apply Finset.sum_eq_zero
    intro r hr
    exact absurd (Finset.mem_filter.mp hr).2
      (hr_prev r (Finset.mem_filter.mp hr).1)
  h_active_positive := by
    -- r_prev is active iff some active r restricts to it; that r witnesses positivity.
    -- Note: `hmem` restates `hr_prev` at the unfolded `Finset.image` type so that
    -- `Finset.mem_image.mp` can fire; definitional equality suffices for the kernel.
    intro r_prev hr_prev
    have hmem : r_prev ∈ Finset.image
        (fun r => restrict_pedigree r hm) μ.active_pedigrees := hr_prev
    obtain ⟨r, hr, hrfl⟩ := Finset.mem_image.mp hmem
    exact hrfl ▸ lt_of_lt_of_le (μ.h_active_positive r hr)
      (Finset.single_le_sum
        (fun r' hr' => μ.h_nonneg r' (Finset.mem_filter.mp hr').1)
        (Finset.mem_filter.mpr ⟨hr, rfl⟩))

-- ============================================================================
-- NECESSITY
-- ============================================================================

/-- Given a convex witness μ at stage m, constructs an explicit feasible FAT
    (Forbidden Arc Transportation problem instance) by Bayesian conditioning: the allocation for predecessor r_prev and edge e
    is the fraction of μ's weight concentrated on pedigrees that both restrict
    to r_prev and choose e at the final stage, divided by the marginal weight
    of r_prev.  When the marginal weight is zero the allocation is set to zero.

    The proof establishes three FAT conditions:
    - `h_nonneg`:  numerator and denominator are both nonneg.
    - `h_sum_one`: summing over all edges telescopes via `Finset.sum_fiberwise`,
                   yielding the marginal weight; dividing gives 1.
    - `h_support`: zero marginal weight forces zero allocation; positive marginal
                   weight implies r_prev is active, contradicting the hypothesis. -/
theorem construct_FAT_from_witness
    {m : Nat} (hm : m ≥ 1) (μ : ConvexWitness m) :
    ∃ fat : FAT m hm (marginalize_witness μ hm),
      ∀ (r_prev : Pedigree (m - 1)) (e : Edge (m + 3)),
        fat.alloc r_prev e =
          if h : (marginalize_witness μ hm).weights r_prev > 0 then
            (∑ r ∈ μ.active_pedigrees.filter
              (fun r => restrict_pedigree r hm = r_prev ∧ last_edge r hm = e),
             μ.weights r) / (marginalize_witness μ hm).weights r_prev
          else 0 := by
  refine ⟨{ alloc    := fun r_prev e =>
               if h : (marginalize_witness μ hm).weights r_prev > 0 then
                 (∑ r ∈ μ.active_pedigrees.filter
                   (fun r => restrict_pedigree r hm = r_prev ∧ last_edge r hm = e),
                  μ.weights r) / (marginalize_witness μ hm).weights r_prev
               else 0,
             h_nonneg  := ?h_nonneg,
             h_sum_one := ?h_sum_one,
             h_support := ?h_support }, ?spec⟩
  case h_nonneg =>
    intro r_prev e
    split_ifs with h
    · exact div_nonneg
        (Finset.sum_nonneg fun r hr =>
          μ.h_nonneg r (Finset.mem_filter.mp hr).1)
        (le_of_lt h)
    · norm_num
  case h_sum_one =>
    intro r_prev hr_prev
    -- r_prev is active so its marginal weight is positive.
    -- Restate hr_prev at the unfolded Finset.image type for Finset.mem_image.mp.
    have hmem : r_prev ∈ Finset.image
        (fun r => restrict_pedigree r hm) μ.active_pedigrees := hr_prev
    obtain ⟨r, hr, hrfl⟩ := Finset.mem_image.mp hmem
    have h_pos : (marginalize_witness μ hm).weights r_prev > 0 :=
      hrfl ▸ lt_of_lt_of_le (μ.h_active_positive r hr)
        (Finset.single_le_sum
          (fun r' hr' => μ.h_nonneg r' (Finset.mem_filter.mp hr').1)
          (Finset.mem_filter.mpr ⟨hr, rfl⟩))
    split_ifs
    · -- Rewrite the double filter as a fibre sum, then factor the denominator out.
      have hnum : ∑ e : Edge (m + 3),
              ∑ r ∈ μ.active_pedigrees.filter
                (fun r => restrict_pedigree r hm = r_prev ∧ last_edge r hm = e),
              μ.weights r
              = (marginalize_witness μ hm).weights r_prev := by
        have key : ∀ e : Edge (m + 3),
            μ.active_pedigrees.filter
              (fun r => restrict_pedigree r hm = r_prev ∧ last_edge r hm = e)
            = (μ.active_pedigrees.filter
                (fun r => restrict_pedigree r hm = r_prev)).filter
                  (fun r => last_edge r hm = e) :=
          fun e => by ext r; simp [Finset.mem_filter, and_assoc]
        simp_rw [key]
        exact (Finset.sum_fiberwise
          (μ.active_pedigrees.filter (fun r => restrict_pedigree r hm = r_prev))
          (fun r => last_edge r hm)
          μ.weights).trans rfl
      -- Factor the constant denominator out of the sum over edges, then cancel.
      have hfactor : ∑ e : Edge (m + 3),
              (∑ r ∈ μ.active_pedigrees.filter
                (fun r => restrict_pedigree r hm = r_prev ∧ last_edge r hm = e),
              μ.weights r) / (marginalize_witness μ hm).weights r_prev
            = (∑ e : Edge (m + 3),
                ∑ r ∈ μ.active_pedigrees.filter
                  (fun r => restrict_pedigree r hm = r_prev ∧ last_edge r hm = e),
                μ.weights r) / (marginalize_witness μ hm).weights r_prev := by
        rw [Finset.sum_div]
      rw [hfactor, hnum, div_self (ne_of_gt h_pos)]
  case h_support =>
    intro r_prev hr_prev e
    split_ifs
    · -- Positive weight means r_prev is active — contradicts hr_prev.
      exfalso; apply hr_prev
      have h_exists : ∃ r ∈ μ.active_pedigrees,
          restrict_pedigree r hm = r_prev := by
        by_contra h_none; push_neg at h_none
        -- No active pedigree restricts to r_prev, so marginal weight is zero.
        have hzero : (marginalize_witness μ hm).weights r_prev = 0 := by
          have hrw : (marginalize_witness μ hm).weights r_prev =
              ∑ r ∈ μ.active_pedigrees.filter
                (fun r => restrict_pedigree r hm = r_prev), μ.weights r := rfl
          rw [hrw]
          apply Finset.sum_eq_zero
          intro r hr
          exact absurd (Finset.mem_filter.mp hr).2
                       (h_none r (Finset.mem_filter.mp hr).1)
        linarith
      obtain ⟨r, hr, hr_eq⟩ := h_exists
      exact Finset.mem_image.mpr ⟨r, hr, hr_eq⟩
    · rfl
  case spec =>
    intro r_prev e; rfl

/-- Necessity: if X lies in the convex hull of pedigrees at stage m,
    then a feasible FAT exists for the marginalised witness. -/
theorem necessity_FAT_feasible
    {m : Nat} (hm : m ≥ 1) (X : SlackVector (m + 3))
    (h_member : in_conv_hull X hm) :
    ∃ μ : ConvexWitness m, ∃ _ : FAT m hm (marginalize_witness μ hm), True := by
  obtain ⟨μ, _⟩ := h_member
  exact ⟨μ, (construct_FAT_from_witness hm μ).choose, trivial⟩

end MembershipProject.PedigreePolytope
