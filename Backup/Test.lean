import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic

-- Test that imports work
#check ℝ
#check Finset.sum
#check Finset.biUnion

example : ℝ := 0

example (s : Finset ℕ) : ℕ := s.sum id
