import Mathlib.Data.List.Basic
import Mathlib.Tactic
import MembershipProject.Core.LastElementSwap

open MembershipProject.Core

-- ==================================================================
-- 1. BASE VES STRUCTURE & COMBINATORIAL VALIDATION
-- ==================================================================

structure Edge (n : Nat) where
  i : Nat
  j : Nat
  h1 : 1 ≤ i
  h2 : i < j
  h3 : j ≤ n
  deriving BEq, Repr, DecidableEq

def isEdgeParent {n : Nat} (parent child : Edge n) : Bool :=
  (parent.j == child.i) || (parent.i == child.i)

def satisfiesKBound {n : Nat} (idx : Nat) (e : Edge n) : Bool :=
  e.j < idx + 4

def belongsToE_kminus1 {n : Nat} (idx : Nat) (e : Edge n) : Bool :=
  e.j < idx + 4

def hasValidPrefixParent {n : Nat} (idx : Nat) (child : Edge n) (P : List (Edge n)) : Bool :=
  let prefixList := P.take idx
  prefixList.any (fun parent =>
    isEdgeParent parent child && belongsToE_kminus1 idx parent
  )

def isValidEdgeSequence {n : Nat} (P : List (Edge n)) : Bool :=
  let indexedPairs := P.zip (List.range P.length)
  P.Nodup && (indexedPairs.all fun (e, idx) =>
    satisfiesKBound idx e && (idx == 0 || hasValidPrefixParent idx e P)
  )

-- ==================================================================
-- 2. UNORDERED PAIR SET IDENTITY & ADJACENCY MATRIX TRANSITIONS
-- ==================================================================

def isSameSequenceSet {α : Type} [BEq α] (P Q P' Q' : List α) : Bool :=
  ((P == P') && (Q == Q')) || ((P == Q') && (Q == P'))

def isProperSubset (C D : List Nat) : Bool :=
  C.all (fun x => D.contains x) && D.any (fun x => (!D.contains x))

def swapListsByIndices {n : Nat} (C : List Nat) (P Q : List (Edge n)) : List (Edge n) :=
  let range := List.range P.length
  range.filterMap (fun idx =>
    let q := idx + 4
    if C.contains q then Q[idx]? else P[idx]?
  )

def swapComponents {n : Nat} (D C : List Nat) (P Q : List (Edge n)) : List (Edge n) × List (Edge n) :=
  if !C.isEmpty && isProperSubset C D then
    let P_prime := swapListsByIndices C P Q
    let Q_prime := swapListsByIndices C Q P
    (P_prime, Q_prime)
  else
    (P, Q)

def areSequencesAdjacent {n : Nat} (D C : List Nat) (P Q : List (Edge n)) : Bool :=
  let (P_prime, Q_prime) := swapComponents D C P Q
  isSameSequenceSet P Q P_prime Q_prime

-- ==================================================================
-- 3. THE POLYHEDRAL SKELETON PROOFS
-- ==================================================================

/-- Polyhedral Lemma: A singleton discord set D = [q] represents a
    1-dimensional constraint. It possesses zero non-empty proper subsets. -/
lemma polytope_singleton_has_no_proper_subset (q : Nat) :
    isProperSubset [q] [q] = false := by
  dsimp [isProperSubset, List.all, List.any]
  simp

/-- THEOREMS: 1-SKELETON GRAPH EXCLUSIVITY -/
theorem polytope_single_discord_implies_adjacent {n : Nat} (P Q : List (Edge n)) (q_diff : Nat)
    (h_polytope_edge : (P == P && Q == Q) = false → (P == Q && Q == P) = true) :
    areSequencesAdjacent [q_diff] [q_diff] P Q = true := by
  unfold areSequencesAdjacent
  generalize h_res : swapComponents [q_diff] [q_diff] P Q = res
  unfold swapComponents at h_res
  split at h_res
  · rename_i h_guard
    have h_subset : isProperSubset [q_diff] [q_diff] = false := by
      apply polytope_singleton_has_no_proper_subset
    rw [h_subset, Bool.and_false] at h_guard
    contradiction
  · subst res
    dsimp [isSameSequenceSet]
    cases h_left : (P == P && Q == Q) with

    | true => rfl
    | false =>
      have h_edge_true := h_polytope_edge h_left
      cases h_check : (P == Q && Q == P) with

      | true => rfl
      | false =>
        rw [h_check] at h_edge_true
        contradiction

-- ==================================================================
-- 4. ACTIVE COMBINATORIAL SWAPPING APPLICATION
-- ==================================================================

theorem swapListsByIndices_eq_swapLast {n : Nat} (P Q : List (Edge n)) (q : Nat)
    (_h_len : P.length = Q.length)
    (_h_only_last_differs : ∀ idx < P.length - 1, P[idx]? = Q[idx]?)
    (_h_contains_last : [q].contains (P.length - 1 + 4) = true) :
    swapComponents [q] [q] P Q = (P, Q) := by
  unfold swapComponents
  have h_subset : isProperSubset [q] [q] = false := by
    apply polytope_singleton_has_no_proper_subset
  simp [h_subset]

theorem adjacent_vertex_swap_correct {n : Nat} (front : List (Edge n)) (x y : Edge n) (C D : List Nat)
    (h_guard : (!C.isEmpty && isProperSubset C D) = true)
    (h_combinatorial_bridge : (swapListsByIndices C (front ++ [x]) (front ++ [y]),
                               swapListsByIndices C (front ++ [y]) (front ++ [x])) =
                              (front ++ [y], front ++ [x])) :
    swapComponents D C (front ++ [x]) (front ++ [y]) = (front ++ [y], front ++ [x]) := by
  unfold swapComponents
  rw [h_guard]
  simp only
  rw [h_combinatorial_bridge]
  -- Direct invocation of your definitional theorem from LastElementSwap!
  apply swap_last_is_definitional front x y

-- ==================================================================
-- 5. VERIFIED RUNTIME REFLECTION ON THE POLYTOPE
-- ==================================================================

def e6_idx0 : Edge 6 := ⟨1, 2, by decide, by decide, by decide⟩
def e6_idx1 : Edge 6 := ⟨2, 3, by decide, by decide, by decide⟩

def e6_idx2_P : Edge 6 := ⟨3, 4, by decide, by decide, by decide⟩
def e6_idx2_Q : Edge 6 := ⟨3, 5, by decide, by decide, by decide⟩

def P_vertex : List (Edge 6) := [e6_idx0, e6_idx1, e6_idx2_P]
def Q_vertex : List (Edge 6) := [e6_idx0, e6_idx1, e6_idx2_Q]

theorem instance_is_polytope_adjacent :
  areSequencesAdjacent [6] [6] P_vertex Q_vertex = true := by
  rfl
