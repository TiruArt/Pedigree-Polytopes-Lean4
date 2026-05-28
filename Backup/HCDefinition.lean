import Mathlib.Combinatorics
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- A cycle is Hamiltonian if it visits every vertex exactly once. -/
def IsHamiltonianCycle (p : G.Walk v v) : Prop :=
  p.IsCycle ∧ ∀ (u : V), u ∈ p.support
--import Mathlib.Combinatorics.SimpleGraph.Connectivity

-- Check if a graph is connected
example {V : Type*} (G : SimpleGraph V) : G.Connected ↔ G.Preconnected ∧ Nonempty V :=
  G.connected_iff_preconnected_and_nonempty
