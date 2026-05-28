-- Core/N_Checking_Welded2_T.lean
-- Welding relation between discords of two pedigrees.
import Init.Data.List.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.FinEnum
import MembershipProject.Core.N_Discords
import MembershipProject.Core.N_RestrictionFull

namespace MembershipProject.Core
-- Define the type alias for a triplet
structure Triplet where
  first : Nat
  second : Nat
  third : Nat
deriving DecidableEq

-- Define the comparison function using your definition
def findDiscords {α : Type} [DecidableEq α] (P Q : List α) : List Nat :=
  (List.zip P Q).mapIdx (fun i (p, q) => if p ≠ q then some i else none)
  |>.filterMap id

-- Example usage
def list1 : List[t:Triplet] := [(1, 2, 3), (1, 2, 4), (1, 4, 5), (4, 5, 6)]
def list2 : List[t:Triplet] := [(1, 2, 3), (1, 3, 4), (3, 4, 5), (4, 5, 6)]

-- Results in [1, 2] (indices of the differing triplets)
#eval findDiscords list1 list2


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


end MembershipProject.Core
