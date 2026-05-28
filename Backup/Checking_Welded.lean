-- Core/N_Checking_Welded2_T.lean
-- Welding relation between discords of two pedigrees.
import Init.Data.List.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.FinEnum
-- Note: Commented out local imports that require external files to compile
import MembershipProject.Core.N_Discords
import MembershipProject.Core.N_RestrictionFull

namespace MembershipProject.Core

-- Define the type alias for a triplet
structure Triplet where
  first : Nat
  second : Nat
  third : Nat
deriving DecidableEq, Repr

-- Define the comparison function (List.mapIdx takes arguments in order: i, x)
def findDiscords {α : Type} [DecidableEq α] (P Q : List α) : List Nat :=
  (List.zip P Q).mapIdx (fun i (p, q) => if p ≠ q then some i else none)
  |>.filterMap id

-- Example usage (Provide exact types for lists)
def list1 : List Triplet := [{first := 1, second := 2, third := 3}, {first := 1, second := 2, third := 4}, {first := 1, second := 4, third := 5}, {first := 4, second := 5, third := 6}]
def list2 : List Triplet := [{first := 1, second := 2, third := 3}, {first := 1, second := 3, third := 4}, {first := 3, second := 4, third := 5}, {first := 4, second := 5, third := 6}]
def list3 : List Triplet := [{first := 1, second := 2, third := 3}, {first := 2, second := 3, third := 4}, {first := 2, second := 4, third := 5}, {first := 2, second := 5, third := 6}]
def list4 : List Triplet := [{first := 1, second := 2, third := 3}, {first := 1, second := 3, third := 4}, {first := 3, second := 4, third := 5}, {first := 1, second := 4, third := 6}]

-- Results in [1, 2] (indices of the differing triplets)
#eval findDiscords list1 list2
#eval findDiscords list1 list3
#eval findDiscords list1 list4
#eval findDiscords list2 list3
#eval findDiscords list2 list4
#eval findDiscords list3 list4

/-- Two discords q_l < q_m are welded if either:
    - Generator reason: the larger endpoint of the edge in one pedigree at q_m equals q_l,
      and the edge at q_l in the other pedigree shares the smaller endpoint.
    - Uniqueness reason: the edge used by one pedigree at q_m appears earlier in the other pedigree.
-/


def welded {n : ℕ} (P Q : Pedigree n) (q_l q_m : ℕ)
    (_ : q_l ∈ discords P Q) (_ : q_m ∈ discords P Q) (_ : q_l < q_m) : Prop :=
  let (a, b) := edge_at P q_m
  let (c, d) := edge_at Q q_m
  let (e, f) := edge_at P q_l
  let (g, h) := edge_at Q q_l
  (-- Generator reason via b
   (b > 3 ∧ b = q_l ∧ (g = a ∨ h = a)) ∨
   -- Generator reason via d
   (d > 3 ∧ d = q_l ∧ (e = c ∨ f = c))) ∨
  (-- Uniqueness reason: (a,b) appears in Q earlier
   (∃ s, 4 ≤ s ∧ s < q_m ∧ edge_at Q s = (a, b)) ∨
   -- Uniqueness reason: (c,d) appears in P earlier
   (∃ s, 4 ≤ s ∧ s < q_m ∧ edge_at P s = (c, d)))


#eval welded 6:ℕ list1 list2 1 2 -- Example usage (requires actual Pedigree instances and discords)

end MembershipProject.Core
