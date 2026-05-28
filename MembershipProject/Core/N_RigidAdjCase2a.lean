-- Core/N_RigidAdjCase2a.lean
-- Sub-case [1] of Theorem adjacencytheorem (Chapter 6, Arthanari 2023).
--
-- Setting: P1, P2 ∈ R_k (rigid pedigrees in P_{k+1}).
-- Case: e¹_{k-1} = e²_{k-1} (same link tail), e¹_k ≠ e²_k (different link head).
--
-- Proof: Assuming P1 and P2 are non-adjacent, the swap pedigree P3 ends
-- with the same link tail as P1 (only one choice since e¹_{k-1} = e²_{k-1}).
-- P3 ends with L1 or L2 → P_unique(L) is not unique → contradiction (huniq).
--
-- Stated for List (Edge n) (edge sequences via PedigreeBijection).
-- Reference: Arthanari, T.S. Pedigree Polytopes, Springer Nature 2023, Chapter 6.

import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace MembershipProject.Core

-- Edge sequence validity (from SwappableImpliesNonAdjacent.lean)
structure Edge (n : Nat) where
  i : Nat
  j : Nat
  h1 : 1 ≤ i
  h2 : i < j
  h3 : j ≤ n
  deriving BEq, DecidableEq

def swapListsByIndicesAux {n : Nat} (C : List Nat) (P Q : List (Edge n)) (offset : Nat) :
    List (Edge n) :=
  match P, Q with
  | [], _ => []
  | _, [] => []
  | p :: pt, q :: qt =>
    if C.contains (offset + 4) then
      q :: swapListsByIndicesAux C pt qt (offset + 1)
    else
      p :: swapListsByIndicesAux C pt qt (offset + 1)

def swapListsByIndices {n : Nat} (C : List Nat) (P Q : List (Edge n)) : List (Edge n) :=
  swapListsByIndicesAux C P Q 0

/-- Sub-case [1]: same last-but-one edge, different last edge.
    P1, P2 are valid edge sequences (via PedigreeBijection equivalence).
    P3 = swapListsByIndices C P1 P2: valid, P3 ≠ P1, P3 ≠ P2.
    P3's last two edges ∈ {P1's, P2's} at each position.
    hsl: same last-but-one → P3 ends with same last-but-one as P1.
    P3 ends with L1 or L2 → huniq → P3 = P1 or P3 = P2 → contradiction. -/
theorem adj_case2a {n : Nat} (P1 P2 : List (Edge n))
    (_hlen : P1.length = P2.length)
    (_hne  : P1 ≠ P2)
    -- Same last-but-one edge: e¹_{k-1} = e²_{k-1}
    (hsl   : P1.dropLast.getLast? = P2.dropLast.getLast?)
    -- Unique path: each link determines exactly one valid edge sequence
    (huniq1 : ∀ R : List (Edge n), R ≠ P1 →
                R.dropLast.getLast? = P1.dropLast.getLast? →
                R.getLast? = P1.getLast? → False)
    (huniq2 : ∀ R : List (Edge n), R ≠ P2 →
                R.dropLast.getLast? = P2.dropLast.getLast? →
                R.getLast? = P2.getLast? → False)
    -- C is a proper nonempty subset of discords (from non-adjacency assumption)
    (C     : List Nat) (_hC_ne : C ≠ [])
    -- P3 = swap(P1,P2,C): P3 ≠ P1, P3 ≠ P2
    (hP3ne1 : swapListsByIndices C P1 P2 ≠ P1)
    (hP3ne2 : swapListsByIndices C P1 P2 ≠ P2)
    -- P3's last-but-one ∈ {P1's, P2's} = {P1's} (hsl)
    (hP3sl  : (swapListsByIndices C P1 P2).dropLast.getLast? =
              P1.dropLast.getLast?)
    -- P3's last ∈ {P1's last, P2's last}
    (hP3last : (swapListsByIndices C P1 P2).getLast? = P1.getLast? ∨
               (swapListsByIndices C P1 P2).getLast? = P2.getLast?) :
    False := by
  -- P3 ends with L1 or L2
  rcases hP3last with h | h
  · -- P3 ends with L1: huniq1 → P3 = P1 → contradiction
    exact huniq1 (swapListsByIndices C P1 P2) hP3ne1 hP3sl h
  · -- P3 ends with L2: huniq2 → P3 = P2 → contradiction
    -- P3's last-but-one = P1's = P2's (hsl) = P2's last-but-one
    exact huniq2 (swapListsByIndices C P1 P2) hP3ne2
      (hP3sl.trans hsl) h

end MembershipProject.Core
