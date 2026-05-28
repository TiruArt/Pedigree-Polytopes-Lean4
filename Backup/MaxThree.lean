import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
/-- Proves that the maximum of three numbers is
the largest when they are in strictly increasing order.
-/
theorem max_of_three {i j k : ℕ} (h1 : i < j) (h2 : j < k) :
  max i (max j k) = k := by
  -- 1. Resolve the inner max: max j k = k because j < k
  rw [max_eq_right h2.le]
  -- 2. Resolve the remaining max: max i k = k because i < k
  have hik : i < k := lt_trans h1 h2
  rw [max_eq_right hik.le]
