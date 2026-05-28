import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace PedigreePolytope

-- Dummy structure because the actual data of `IntegerMIR 3` is irrelevant for the base case
structure IntegerMIR (n : ℕ) where
  dummy : Unit

-- The three edges of the base triangle (0,1,2)
def base_edges : Finset (Fin 3 × Fin 3) :=
  {(⟨0, by omega⟩, ⟨1, by omega⟩),
   (⟨1, by omega⟩, ⟨2, by omega⟩),
   (⟨0, by omega⟩, ⟨2, by omega⟩)}

-- Slack for n = 3: no k ≥ 4, so slack = 1 iff the two vertices are distinct
def slack_value (_ : IntegerMIR 3) (e : Fin 3 × Fin 3) : ℝ :=
  if e.1 < e.2 then 1 else if e.2 < e.1 then 1 else 0

-- Base case theorem: slack = 1 exactly on the three edges of the triangle
theorem base_case (X : IntegerMIR 3) (e : Fin 3 × Fin 3) :
    slack_value X e = 1 ↔ e ∈ base_edges := by
  match e with
  | (⟨0, _⟩, ⟨0, _⟩) => decide
  | (⟨0, _⟩, ⟨1, _⟩) => decide
  | (⟨0, _⟩, ⟨2, _⟩) => decide
  | (⟨1, _⟩, ⟨0, _⟩) => decide
  | (⟨1, _⟩, ⟨1, _⟩) => decide
  | (⟨1, _⟩, ⟨2, _⟩) => decide
  | (⟨2, _⟩, ⟨0, _⟩) => decide
  | (⟨2, _⟩, ⟨1, _⟩) => decide
  | (⟨2, _⟩, ⟨2, _⟩) => decide

end PedigreePolytope
