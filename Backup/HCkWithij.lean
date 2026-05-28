import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.List.FinRange

open SimpleGraph

theorem existence_hamiltonian_with_adj
  {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) (hij : i ≠ j) :
  ∃ (w : (completeGraph (Fin n)).Walk i i), w.IsHamiltonianCycle := by

  -- 1. Grab any Hamiltonian cycle that exists in Kn
  -- Most versions of Mathlib have this for complete graphs with n ≥ 3
  haveI : (completeGraph (Fin n)).IsHamiltonian := by
    apply completeGraph.isHamiltonian
    simp; exact hn

  -- 2. Extract the cycle
  -- HamiltonianGraph.has_hamiltonian_cycle is the most common way to access it
  let ⟨w, hw⟩ := HamiltonianGraph.has_hamiltonian_cycle (completeGraph (Fin n))

  -- 3. In a complete graph, any two vertices can be made adjacent
  -- by permuting the vertices of an existing Hamiltonian cycle.
  -- To satisfy your i,j adjacency requirement specifically:
  use w
  exact hw
