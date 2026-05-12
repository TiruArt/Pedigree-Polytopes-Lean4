import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.List.Basic
import Mathlib.SetTheory.Cardinal.Finite

open Finset

variable {α : Type*} [DecidableEq α]

/-
1. Finite Sets (`Finset`)
A Finset is a type for finite subsets of a type α.
It can be constructed from a list with no duplicates.
-/

-- Example: Defining a finite set of natural numbers
def A : Finset ℕ := {1, 2, 3, 4, 5}
def B : Finset ℕ := {5, 6, 7, 8, 9, 10}

-- Example: Getting the cardinality (size) of a Finset
#eval A.card -- Output: 5
#eval B.card -- Output: 6
-- Example: Membership test
example : 3 ∈ A := by decide
example : 6 ∉ A := by decide

/-
2. 3-Element Sets (Subsets of a specific size)
We can filter all subsets of a given finite set to find those with a specific cardinality.
The `Finset.powerset` function generates all subsets.
-/

-- A finite type to work with
abbrev MyType : Type := Fin 4

-- The universe of MyType as a Finset
def U : Finset MyType := Finset.univ

-- Definition of a 3-element subset (decidable predicate)
def is_three_element_subset (s : Finset MyType) : Prop := s.card = 3

-- Make it decidable
instance : DecidablePred is_three_element_subset := fun s =>
  inferInstanceAs (Decidable (s.card = 3))

-- Finding all 3-element subsets of U
def three_element_subsets : Finset (Finset MyType) :=
  U.powerset.filter is_three_element_subset

-- Evaluation of the 3-element subsets
#eval three_element_subsets.card -- The number of 3-element subsets of a 4-element set is 4

/-
3. Partitions of a Finite Set
A partition of a set S is a collection of non-empty, pairwise disjoint subsets whose union is S.
Mathlib defines partitions more formally in specific modules, but here's a conceptual way to work with the properties.
-/

-- A property for a collection of finsets to be pairwise disjoint
def PairwiseDisjoint (C : Finset (Finset α)) : Prop :=
  ∀ s₁ ∈ C, ∀ s₂ ∈ C, s₁ ≠ s₂ → Disjoint s₁ s₂

-- A property for a collection of finsets to cover the whole set S
def Covers (C : Finset (Finset α)) (S : Finset α) : Prop :=
  ∀ x ∈ S, ∃ s ∈ C, x ∈ s

-- Definition of a partition
structure FinsetPartition (S : Finset α) where
  parts : Finset (Finset α)
  h_nonempty : ∀ s ∈ parts, s.Nonempty
  h_pairwise_disjoint : PairwiseDisjoint parts
  h_covers : Covers parts S
  h_subsets : ∀ s ∈ parts, s ⊆ S

-- Example: A partition of A = {1, 2, 3, 4, 5}
def P_parts : Finset (Finset ℕ) := { {1, 2}, {3, 4}, {5} }
-- Proving the properties for P_parts would involve detailed proofs in Lean, e.g., using decide and ext tactics.

-- Define a type with 3 elements (e.g., Fin 3)
abbrev three_elements_type : Type := Fin 3

-- The elements are 0, 1, 2. We can get the Finset of all elements using `univ`
def S : Finset three_elements_type := univ

-- The cardinality is 3
#eval S.card -- Output: 3

-- The number of partitions of a 3-element set is 5 (Bell number B₃)
