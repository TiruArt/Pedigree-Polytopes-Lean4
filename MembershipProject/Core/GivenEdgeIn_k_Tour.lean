import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Linarith
-- 1. This stops all "failed to compile... noncomputable" errors in this file.
noncomputable section

open SimpleGraph
variable {n : ℕ}
variable {V : Type*} [Fintype V] [DecidableEq V]
/--
In the complete graph, an edge exists between any two vertices
as long as they are not the same vertex.
-/
def complete_adj (u v : Fin n) (h : u ≠ v) : (⊤ : SimpleGraph (Fin n)).Adj u v := h

/--
To show we can visit every vertex once, we just need a
list of all vertices with no duplicates.
-/
theorem complete_graph_path (n : ℕ) :
  ∃ (l : List (Fin n)), l.Nodup ∧ l.length = n := by
  -- We define the list clearly
  let l := Finset.univ.toList (α := Fin n)
  use l
  constructor
  · -- This version specifies which finset we are talking about
    exact Finset.nodup_toList Finset.univ
  · -- Length of Finset.univ.toList is always the cardinality (n)
    simp [l]

/--
If the library theorem is missing, we define the cycle manually.
For a complete graph, ANY sequence of all vertices is a cycle.
-/
-- Checking it for K_5
example : ∃ (l : List (Fin 5)), l.Nodup ∧ l.length = 5 :=
  complete_graph_path 5

#check complete_graph_path 5
/--
Proving the 'Back-Edge' exists between the last element of our
constructed path and the starting vertex i.
-/
theorem back_edge_fix (i j : V) :
  let others := (Finset.univ.erase i).erase j
  ∀ v ∈ others, (⊤ : SimpleGraph V).Adj v i := by
  intro others v h_mem
  -- 1. In a complete graph, we just need to prove v ≠ i
  change v ≠ i

  -- 2. h_mem proves v ∈ (univ.erase i).erase j
  -- We peel off the 'j' layer first
  have h_in_inner : v ∈ Finset.univ.erase i := Finset.mem_of_mem_erase h_mem

  -- 3. Now we prove it's not i using the inner layer
  exact Finset.ne_of_mem_erase h_in_inner

/--
A generic, computable construction of a Hamiltonian path.
This avoids 'Finset' and 'noncomputable' errors entirely.
-/
def make_hc (n : ℕ) (i j : Fin n) : List (Fin n) :=
  -- Generate all vertices as a list, then filter out i and j
  let others := (List.finRange n).filter (λ x => x ≠ i ∧ x ≠ j)
  [i, j] ++ others ++ [i]

-- This will now work without any errors!
#eval make_hc 10 1 2

-- We define the property directly to avoid complex library lemmas
theorem back_edge_no_theorems {V : Type} (i : V) (others : List V) (h_not_empty : others ≠ []) :
  (∀ x ∈ others, x ≠ i) → (completeGraph V).Adj (others.getLast h_not_empty) i := by
  -- Unfold the definition of our graph's adjacency
  unfold completeGraph
  simp

  -- We need to show: others.getLast ≠ i
  intro h_excluded

  -- We know the last element is an element of the list
  let v_last := others.getLast h_not_empty
  have h_is_mem : v_last ∈ others := List.getLast_mem h_not_empty

  -- Our assumption 'h_excluded' says EVERY element in others is not i
  -- So we just apply that logic to v_last
  have h_final : v_last ≠ i := h_excluded v_last h_is_mem

  exact h_final
#eval make_hc 20 5 19
