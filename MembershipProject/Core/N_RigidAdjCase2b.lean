-- Core/N_RigidAdjCase2b.lean
-- Sub-case [2] of Theorem adjacencytheorem (Chapter 6, Arthanari 2023).
--
-- Setting: P1, P2 ∈ R_k (rigid pedigrees in P_{k+1}).
-- Case: e¹_{k-1} ≠ e²_{k-1} (different link tail), e¹_k = e²_k (same link head).
--
-- Proof: Symmetric to Sub-case [1].
-- The swap pedigree P3 ends with the same link head as P1 (only one choice).
-- P3 ends with L1 or L2 → uniqueness of P_unique(L) violated → contradiction.
--
-- Stated for List (Edge n) (edge sequences via PedigreeBijection).
-- Reference: Arthanari, T.S. Pedigree Polytopes, Springer Nature 2023, Chapter 6.

import Mathlib.Data.List.Basic
import Mathlib.Tactic
import MembershipProject.Core.N_RigidAdjCase2a

namespace MembershipProject.Core

theorem adj_case2b {n : Nat} (P1 P2 : List (Edge n))
    (_hlen  : P1.length = P2.length)
    (_hne   : P1 ≠ P2)
    -- Same last edge: e¹_k = e²_k
    (hhl    : P1.getLast? = P2.getLast?)
    (huniq1 : ∀ R : List (Edge n), R ≠ P1 →
                R.dropLast.getLast? = P1.dropLast.getLast? →
                R.getLast? = P1.getLast? → False)
    (huniq2 : ∀ R : List (Edge n), R ≠ P2 →
                R.dropLast.getLast? = P2.dropLast.getLast? →
                R.getLast? = P2.getLast? → False)
    (C      : List Nat) (_hC_ne : C ≠ [])
    (hP3ne1 : swapListsByIndices C P1 P2 ≠ P1)
    (hP3ne2 : swapListsByIndices C P1 P2 ≠ P2)
    -- P3's last = P1's = P2's (hhl: equal)
    (hP3last : (swapListsByIndices C P1 P2).getLast? = P1.getLast?)
    -- P3's last-but-one ∈ {P1's, P2's}
    (hP3sl   : (swapListsByIndices C P1 P2).dropLast.getLast? =
               P1.dropLast.getLast? ∨
               (swapListsByIndices C P1 P2).dropLast.getLast? =
               P2.dropLast.getLast?) :
    False := by
  rcases hP3sl with h | h
  · exact huniq1 (swapListsByIndices C P1 P2) hP3ne1 h hP3last
  · exact huniq2 (swapListsByIndices C P1 P2) hP3ne2 h (hP3last.trans hhl)

end MembershipProject.Core
