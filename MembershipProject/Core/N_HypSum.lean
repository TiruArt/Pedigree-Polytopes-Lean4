-- N_HypSum.lean
-- Defines isDefault, defaultEdge, and hypSum independently.

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_PedigreeDefinition
import Mathlib.Tactic

namespace MembershipProject.Core

/-- Default edge at layer k: e^k = (k-2, k-1, k) -/
def defaultEdge (k : ℕ) : Triple := (k-2, k-1, k)

/-- Is this triple a default edge? -/
def isDefault (t : Triple) : Bool :=
  t.i + 2 == t.k && t.j + 1 == t.k

/-- Hyperplane sum: sum of C(t) over non-default triangles of P -/
noncomputable def hypSum {n : ℕ} (C : Triple → ℚ) (P : Pedigree n) : ℚ :=
  ((P.triangles.filter (fun t => !isDefault t)).map C).sum

end MembershipProject.Core
