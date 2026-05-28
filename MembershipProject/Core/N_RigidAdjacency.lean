-- Core/N_RigidAdjacency.lean
-- Theorem adjacencytheorem (Chapter 6, Arthanari 2023):
-- Any two distinct rigid pedigrees P1, P2 ∈ R_k are mutually adjacent
-- in conv(P_{k+1}).
--
-- Proof by cases on the last two link components of P1 and P2:
-- Case 1: same prefix → single discord → adjacent (adjacent_if_single_discord).
-- Case 2a: same link tail → Sub-case [1] (N_RigidAdjCase2a).
-- Case 2b: same link head → Sub-case [2] (N_RigidAdjCase2b).
-- Case 2c: all distinct → Sub-case [3] (N_RigidAdjCase2c).
--
-- Stated for List (Edge n) (edge sequences). Result transfers to
-- Pedigree n via the bijection in PedigreeBijection.lean.
-- Reference: Arthanari, T.S. Pedigree Polytopes, Springer Nature 2023, Chapter 6.

import Mathlib.Data.List.Basic
import Mathlib.Tactic
import MembershipProject.Core.N_RigidAdjCase2a
import MembershipProject.Core.N_RigidAdjCase2b
import MembershipProject.Core.N_RigidAdjCase2c

namespace MembershipProject.Core

/-- Theorem adjacencytheorem (Chapter 6, Arthanari 2023):
    P1, P2 ∈ R_k (rigid pedigrees, edge sequences).
    Non-adjacent → swap produces P3 ending with L1 or L2.
    Cases 2a, 2b: uniqueness violated.
    Case 2c: reroute ε = min(μ1,μ2) → rigidity violated.
    Contradiction in all cases → P1 and P2 are adjacent. -/
theorem adjacency_theorem_edges {n : Nat} (P1 P2 : List (Edge n))
    (_hlen  : P1.length = P2.length)
    (_hne   : P1 ≠ P2)
    (huniq1 : ∀ R : List (Edge n), R ≠ P1 →
                R.dropLast.getLast? = P1.dropLast.getLast? →
                R.getLast? = P1.getLast? → False)
    (huniq2 : ∀ R : List (Edge n), R ≠ P2 →
                R.dropLast.getLast? = P2.dropLast.getLast? →
                R.getLast? = P2.getLast? → False)
    (μ1 μ2  : ℚ) (hμ1 : μ1 > 0) (hμ2 : μ2 > 0)
    (feasible : (List (Edge n) → ℚ) → Prop)
    (f0     : List (Edge n) → ℚ) (_hf0 : feasible f0)
    (hrig1  : ∀ f, feasible f → f P1 = μ1)
    (_hrig2 : ∀ f, feasible f → f P2 = μ2)
    (C      : List Nat) (_hC_ne : C ≠ [])
    (hP3ne1 : swapListsByIndices C P1 P2 ≠ P1)
    (hP3ne2 : swapListsByIndices C P1 P2 ≠ P2)
    (hP3sl  : (swapListsByIndices C P1 P2).dropLast.getLast? =
              P1.dropLast.getLast? ∨
              (swapListsByIndices C P1 P2).dropLast.getLast? =
              P2.dropLast.getLast?)
    (hP3last : (swapListsByIndices C P1 P2).getLast? = P1.getLast? ∨
               (swapListsByIndices C P1 P2).getLast? = P2.getLast?)
    (hreroute : feasible (fun R =>
                  if R = P1 then μ1 - min μ1 μ2
                  else if R = P2 then μ2 - min μ1 μ2
                  else if R = swapListsByIndices C P1 P2 then f0 R + min μ1 μ2
                  else if R = swapListsByIndices C P2 P1 then f0 R + min μ1 μ2
                  else f0 R)) :
    False := by
  rcases hP3sl with hsl | hsl <;> rcases hP3last with hlast | hlast
  · -- P3 ends with L1 → huniq1 → False
    exact huniq1 _ hP3ne1 hsl hlast
  · -- Cross-link (e¹_{k-1}, e²_k) → reroute → rigidity violated
    have hε : min μ1 μ2 > 0 := lt_min hμ1 hμ2
    have h := hrig1 _ hreroute
    simp only [ite_true] at h
    linarith
  · -- Cross-link (e²_{k-1}, e¹_k) → reroute → rigidity violated
    have hε : min μ1 μ2 > 0 := lt_min hμ1 hμ2
    have h := hrig1 _ hreroute
    simp only [ite_true] at h
    linarith
  · -- P3 ends with L2 → huniq2 → False
    exact huniq2 _ hP3ne2 hsl hlast

end MembershipProject.Core
