-- File No. 4-1 - N_DesirableDef.lean
--
-- Alternative Finset-based definition of Pedigree.
-- A Pedigree is represented as a Finset (Finset ℕ) — a set of
-- 3-element subsets of ℕ — rather than as a List Triple.
--
-- This formulation is used in files that require decidability
-- of Pedigree membership (via Lean 4's automatic instance synthesis).
--
-- RELATIONSHIP TO N_PedigreeDefinition (File No. 4):
-- Both define the same mathematical object — a valid sequence of
-- Multistage Insertions. This formulation uses Finset for
-- computational verification; N_PedigreeDefinition uses List Triple
-- for proof-theoretic development.
--
-- THREE PREDICATES:
--   isPreSolution n S : structural validity (size, triangle size, unique layer rep)
--   isSolution    n S : isPreSolution + distinct insertion pairs for layers ≥ 4
--   Pedigree      n S : isSolution + generator condition (Multistage Insertion)
--
-- COMPUTATIONAL VERIFICATION:
--   All three predicates are automatically Decidable — verified
--   by native_decide/#decide for concrete cases n = 5, 6.
--
-- Reference: Arthanari, T.S. arXiv:2507.09069v1 [math.CO].

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Finset

-- ============================================================
-- PREDICATES
-- ============================================================

/-- isPreSolution n S: structural validity of S as a pedigree candidate.
    - S has exactly n-2 triangles (layers 3 through n)
    - Each triangle has exactly 3 elements
    - For each layer k ∈ [3,n], there is a unique triangle in S
      whose maximum element is k (the triangle recording insertion of k) -/
def isPreSolution (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  S.card = n - 2 ∧
  (∀ t ∈ S, t.card = 3) ∧
  (∀ k ∈ Finset.Icc 3 n, ∃ t ∈ S, (k ∈ t ∧ ∀ x ∈ t, x ≤ k) ∧
    ∀ t' ∈ S, (k ∈ t' ∧ ∀ x ∈ t', x ≤ k) → t' = t)

/-- isSolution n S: isPreSolution + distinct insertion pairs.
    For any two triangles t1, t2 at layers k1 < k2 (both ≥ 4),
    the insertion pairs (t1 ∖ {k1}) and (t2 ∖ {k2}) must differ.
    This corresponds to h_distinct in N_PedigreeDefinition.
    Note: the base triangle at layer 3 is excluded (k ≥ 4 required). -/
def isSolution (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  isPreSolution n S ∧
  ∀ t1 ∈ S, ∀ t2 ∈ S,
    let k1 := t1.max.getD 0
    let k2 := t2.max.getD 0
    (k1 ≥ 4 ∧ k2 ≥ 4 ∧ k1 < k2) → (t1.erase k1) ≠ (t2.erase k2)

/-- Pedigree n S: isSolution + generator condition.
    For each triangle t at layer k with insertion pair (a,b) = t ∖ {k}:
    Either (a,b) ⊆ {1,2,3} (base case: first insertion into 3-tour)
    or there exists a prior triangle t_prev ∈ S whose maximum is b
    and which contains a (generator condition: Multistage Insertion). -/
def Pedigree (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  isSolution n S ∧ ∀ t ∈ S,
    let k    := t.max.getD 0
    let pair := t.erase k
    let a    := pair.min.getD 0
    let b    := pair.max.getD 0
    (pair ⊆ {1, 2, 3}) ∨ (∃ t_prev ∈ S, t_prev.max = some b ∧ a ∈ t_prev)

-- ============================================================
-- DECIDABILITY INSTANCES
-- Lean 4 automatically synthesizes Decidable instances for all
-- three predicates, enabling #decide and native_decide verification.
-- ============================================================

instance (n : ℕ) (S : Finset (Finset ℕ)) : Decidable (isPreSolution n S) := by
  unfold isPreSolution; infer_instance

instance (n : ℕ) (S : Finset (Finset ℕ)) : Decidable (isSolution n S) := by
  unfold isSolution; infer_instance

instance (n : ℕ) (S : Finset (Finset ℕ)) : Decidable (Pedigree n S) := by
  unfold Pedigree; infer_instance

-- ============================================================
-- CONCRETE VERIFICATION (n = 5, 6)
-- ============================================================

-- Test cases for n = 5
def S5_natural : Finset (Finset ℕ) := {{1,2,3}, {2,3,4}, {3,4,5}}
def S5_prime   : Finset (Finset ℕ) := {{1,2,3}, {1,3,4}, {3,4,5}}
def S5_fail    : Finset (Finset ℕ) := {{1,2,3}, {1,2,4}, {3,4,5}}
def S6_natural : Finset (Finset ℕ) := {{1,2,3}, {2,3,4}, {3,4,5}, {4,5,6}}

-- Kernel-validated proofs via #decide
example : Pedigree 5 S5_natural := by decide  -- valid pedigree
example : Pedigree 5 S5_prime   := by decide  -- valid pedigree
example : ¬ Pedigree 5 S5_fail  := by decide  -- invalid: repeated pair (1,2)
example : Pedigree 6 S6_natural := by decide  -- valid pedigree
