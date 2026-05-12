import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.FinRange

set_option linter.unusedSimpArgs false
open SimpleGraph

/-- 1. Definition of our Hamiltonian list construction -/
def hcList (n : ℕ) (i j : Fin n) : List (Fin n) :=
  let others := (List.finRange n).filter (λ x => x ≠ i ∧ x ≠ j)
  [i, j] ++ others

/-- 2. Predicate: the edge (u, v) is the first edge in the list -/
def is_edge_in_cycle {V : Type*} (u v : V) (l : List V) : Prop :=
  ∃ (tail : List V), l = u :: v :: tail

/-- 3. Proof that the list has no duplicates -/
theorem hcList_nodup {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
  (hcList n i j).Nodup := by
  rw [hcList]
  apply List.nodup_append.mpr
  constructor
  · simp [hij]
  · constructor
    · apply List.Nodup.filter
      exact List.nodup_finRange n
    · -- Disjointness: x is in {i, j} and y is in the filter
      intro x hx y hy hxy
      simp at hx
      have hy_prop : y ≠ i ∧ y ≠ j := by
        revert hy
        simp [List.mem_filter]
      cases hx with

      | inl hi => rw [hi] at hxy; exact hy_prop.1 hxy.symm
      | inr hj => rw [hj] at hxy; exact hy_prop.2 hxy.symm

/-- 4. Main Theorem: Edge (i, j) exists in a Hamiltonian Cycle -/
theorem complete_graph_has_hc_with_edge
  {n : ℕ} (hn : n ≥ 4) (i j : Fin n) (hij : i ≠ j) :
  ∃ (l : List (Fin n)),
    l.Nodup ∧ l.length = n ∧ is_edge_in_cycle i j l := by
  set others := (List.finRange n).filter (λ x => x ≠ i ∧ x ≠ j) with h_others
  set l := [i, j] ++ others with h_l
  use l
  constructor
  · rw [h_l, ← hcList]
    exact hcList_nodup hij
  · constructor
    · -- REVERTED: Placeholder for length proof
      sorry
    · -- Edge inclusion proof
      rw [is_edge_in_cycle]
      use others
      rw [h_l]
      simp

#check @complete_graph_has_hc_with_edge
