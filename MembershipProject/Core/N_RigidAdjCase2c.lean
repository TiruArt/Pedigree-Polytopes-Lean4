-- Core/N_RigidAdjCase2c.lean
-- Sub-case [3] of Theorem adjacencytheorem (Chapter 6, Arthanari 2023).
--
-- Setting: P1, P2 ∈ R_k (rigid pedigrees in P_{k+1}).
-- Case: all four edges distinct (e¹_{k-1} ≠ e²_{k-1} and e¹_k ≠ e²_k).
--
-- Proof: The swap pedigree P3 ends with L1, L2, or a cross-link.
-- L1 or L2: uniqueness of P_unique(L) violated → contradiction (as in [1],[2]).
-- Cross-link: reroute ε = min(μ1,μ2) through the cycle (P3,P4,P1,P2).
--   Net change = 0 (flow cycle), all flows ≥ 0 (ε ≤ μ1, μ2).
--   New flow has μ1-ε on L1 ≠ μ1 → rigidity of L1 violated → contradiction.
--
-- Stated for List (Edge n) (edge sequences via PedigreeBijection).
-- Reference: Arthanari, T.S. Pedigree Polytopes, Springer Nature 2023, Chapter 6.

import Mathlib.Data.List.Basic
import Mathlib.Tactic
import MembershipProject.Core.N_RigidAdjCase2a

namespace MembershipProject.Core

/-- A feasible flow assigns nonneg flows to arcs in F_{k-1}.
    Closed under nonneg cycle additions (rerouting preserves feasibility). -/
def FeasibleFlow (n : Nat) := List (Edge n) → ℚ

/-- Rigidity: arc L has the same flow in EVERY feasible solution to F_{k-1}. -/
def IsRigidArc {n : Nat} (P : List (Edge n)) (μ : ℚ)
    (feasible : FeasibleFlow n → Prop) : Prop :=
  ∀ f : FeasibleFlow n, feasible f → f P = μ

theorem adj_case2c {n : Nat} (P1 P2 : List (Edge n))
    (_hlen  : P1.length = P2.length)
    (_hne   : P1 ≠ P2)
    (_hdsl  : P1.dropLast.getLast? ≠ P2.dropLast.getLast?)
    (_hdlh  : P1.getLast? ≠ P2.getLast?)
    (huniq1 : ∀ R : List (Edge n), R ≠ P1 →
                R.dropLast.getLast? = P1.dropLast.getLast? →
                R.getLast? = P1.getLast? → False)
    (huniq2 : ∀ R : List (Edge n), R ≠ P2 →
                R.dropLast.getLast? = P2.dropLast.getLast? →
                R.getLast? = P2.getLast? → False)
    -- μ1, μ2: fixed arc flows (rigid)
    (μ1 μ2  : ℚ) (hμ1 : μ1 > 0) (hμ2 : μ2 > 0)
    -- Feasibility predicate and base feasible flow f0
    (feasible : FeasibleFlow n → Prop)
    (f0      : FeasibleFlow n) (_hf0 : feasible f0)
    -- Rigidity: every feasible flow has μ1 on P1 and μ2 on P2
    (hrig1   : IsRigidArc P1 μ1 feasible)
    (_hrig2  : IsRigidArc P2 μ2 feasible)
    -- Rerouting by ε = min(μ1,μ2) along cycle (P3,P4,P1,P2) gives feasible flow
    -- (net change = 0 at every node; all flows ≥ 0 since ε ≤ μ1, ε ≤ μ2)
    (C       : List Nat) (_hC_ne : C ≠ [])
    (hP3ne1  : swapListsByIndices C P1 P2 ≠ P1)
    (hP3ne2  : swapListsByIndices C P1 P2 ≠ P2)
    (hP3sl   : (swapListsByIndices C P1 P2).dropLast.getLast? =
               P1.dropLast.getLast? ∨
               (swapListsByIndices C P1 P2).dropLast.getLast? =
               P2.dropLast.getLast?)
    (hP3last : (swapListsByIndices C P1 P2).getLast? = P1.getLast? ∨
               (swapListsByIndices C P1 P2).getLast? = P2.getLast?)
    -- The rerouted flow (decreasing P1,P2 by ε, increasing P3,P4 by ε) is feasible
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
  · -- Cross-link (e¹_{k-1}, e²_k): reroute ε = min(μ1,μ2) → L1 flow = μ1-ε < μ1
    have hε_pos : min μ1 μ2 > 0 := lt_min hμ1 hμ2
    have h := hrig1 _ hreroute
    simp only [ite_true] at h
    linarith
  · -- Cross-link (e²_{k-1}, e¹_k): symmetric
    have hε_pos : min μ1 μ2 > 0 := lt_min hμ1 hμ2
    have h := hrig1 _ hreroute
    simp only [ite_true] at h
    linarith
  · -- P3 ends with L2 → huniq2 → False
    exact huniq2 _ hP3ne2 hsl hlast

end MembershipProject.Core
