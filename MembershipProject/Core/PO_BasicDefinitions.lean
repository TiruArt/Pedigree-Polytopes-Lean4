import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Real.Basic

namespace PedigreeOpt

-- 1. Triangles Δᵏ
def DeltaK (n : ℕ) (k : Fin n) : Finset (Fin n × Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n × Fin n)).filter
    (λ u => u.1 < u.2.1 ∧ u.2.1 < u.2.2 ∧ u.2.2 = k)

-- 2. Common Edge helper
def commonEdge {n : ℕ} (u : Fin n × Fin n × Fin n) : Fin n × Fin n :=
  (u.1, u.2.1)

-- 3. The slack graph
/--
  In your Mathlib version, fromRel takes ONLY the relation.
  It automatically handles symmetry and loopless properties.
-/
def slack_graph (n : ℕ) (u : Sym2 (Fin n) → Real) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => u (Sym2.mk i j) = 1)

end PedigreeOpt
