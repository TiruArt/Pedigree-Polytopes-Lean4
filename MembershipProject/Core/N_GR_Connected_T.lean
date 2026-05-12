-- Core/N_GR_Connected_T.lean
-- Connectedness of G_R defined via edge set.

import Mathlib.Data.Finset.Basic
import MembershipProject.Core.N_Checking_Welded2_T

namespace MembershipProject.Core

/-- Vertices of G_R are the discords. -/
def gr_vertices {n : ℕ} (P Q : Pedigree n) : Finset ℕ :=
  discords P Q

/-- Edge set of G_R: unordered pairs of discords that are welded. -/
def gr_edges {n : ℕ} (P Q : Pedigree n) : Finset (Finset ℕ) :=
  (gr_vertices P Q).powerset.filter (fun e =>
    e.card = 2 ∧
    let s := e.toList
    let q1 := s[0]
    let q2 := s[1]
    welded P Q (min q1 q2) (max q1 q2) (by sorry) (by sorry) (by sorry))

/-- G_R is connected if for any two vertices there is a path using gr_edges. -/
def gr_connected {n : ℕ} (P Q : Pedigree n) : Prop :=
  ∀ v1 v2 ∈ gr_vertices P Q,
    ∃ path : List ℕ,
      path.head = v1 ∧ path.last = v2 ∧
      ∀ i < path.length - 1, {path[i], path[i+1]} ∈ gr_edges P Q

end MembershipProject.Core
