-- Core/N_RigidityGraph_T.lean
-- Rigidity graph G_R(P,Q) as a SimpleGraph on discords.

import Mathlib.Combinatorics.SimpleGraph.Basic
import MembershipProject.Core.N_Checking_Welded2_T

namespace MembershipProject.Core

def rigidityGraph {n : ℕ} (P Q : Pedigree n) : SimpleGraph {q // q ∈ discords P Q} where
  Adj v1 v2 :=
    v1 ≠ v2 ∧
    let q1 := v1.val
    let q2 := v2.val
    welded P Q (min q1 q2) (max q1 q2)
      (by exact (if h : min q1 q2 ∈ discords P Q then h else sorry))
      (by exact (if h : max q1 q2 ∈ discords P Q then h else sorry))
      (by exact (if h : min q1 q2 < max q1 q2 then h else sorry))
  symm := sorry
  loopless := sorry

end MembershipProject.Core
