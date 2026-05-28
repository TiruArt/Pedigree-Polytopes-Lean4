import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Disjoint
import Mathlib.Order.Partition.Finpartition

open Finset

-- Option 1: Using Set-based partitions (simplest)
def IsPartition (S : Set ℕ) (P : Set (Set ℕ)) : Prop :=
  -- All elements of P are subsets of S
  (∀ s ∈ P, s ⊆ S) ∧
  -- All subsets in P are non-empty
  (∀ s ∈ P, s.Nonempty) ∧
  -- All subsets in P are pairwise disjoint
  (∀ s t, s ∈ P → t ∈ P → s ≠ t → Disjoint s t) ∧
  -- The union of all subsets in P is S
  (⋃₀ P = S)

def mySet : Set ℕ := {1, 2, 3, 4}
def p1 : Set (Set ℕ) := {{1, 2}, {3, 4}}
def p2 : Set (Set ℕ) := {{1}, {2, 3}, {4}}

-- Option 2: Manual finset-based partition (recommended)
def IsFinsetPartition (S : Finset ℕ) (P : Finset (Finset ℕ)) : Prop :=
  -- All parts are nonempty
  (∀ s ∈ P, s.Nonempty) ∧
  -- All parts are pairwise disjoint
  (∀ s ∈ P, ∀ t ∈ P, s ≠ t → Disjoint s t) ∧
  -- Union covers S
  (P.biUnion id = S)

def myFinset : Finset ℕ := {1, 2, 3, 4}
def pf1 : Finset (Finset ℕ) := {{1, 2}, {3, 4}}
def pf2 : Finset (Finset ℕ) := {{1}, {2, 3}, {4}}

-- Verify the predicate type-checks
#check IsFinsetPartition myFinset pf1

-- If you want to prove p1 is actually a partition, you can do:
-- lemma pf1_is_partition : IsFinsetPartition myFinset pf1 := by
--   constructor
--   · -- All parts nonempty
--     intro s hs
--     simp [pf1] at hs
--     cases hs with
--     | inl h => simp [h]
--     | inr h => simp [h]
--   constructor
--   · -- All parts disjoint
--     intro s hs t ht hne
--     simp [pf1] at hs ht
--     sorry -- Would need actual proof
--   · -- Union covers
--     simp [pf1, myFinset]
--     sorry -- Would need actual proof
