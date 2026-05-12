import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Sym.Sym2
namespace PedigreeOpt

-- 1. Use 'open scoped' to enable the ∑ notation properly
open Finset SimpleGraph
open scoped BigOperators

variable (s : Fin 3 × Fin 3 → ℝ)

def K3 := SimpleGraph.completeGraph (Fin 3)

theorem slack_is_3tour_hc (n : ℕ) (h_n : n = 3)
  (h_slack : ∀ (i j : Fin 3), i < j → (∑ _k ∈ Icc 4 n, (0 : ℝ)) + s (i, j) = 1) :
  ∀ (i j : Fin 3), i < j → s (i, j) = 1 := by
  intro i j hij
  have range_empty : Icc 4 3 = ∅ := by
    rw [h_n] at *
    exact Icc_eq_empty (by linarith)
  specialize h_slack i j hij
  rw [h_n, range_empty] at h_slack
  simp at h_slack
  exact h_slack

/--
  Fixing 'Sym2.mk' mismatch:
  - Sym2.mk takes ONE argument (a product pair).
  - We use the notation s(i, j) which is shorthand for Sym2.mk (i, j).
-/
theorem slack_is_hc (h_s : ∀ (i j : Fin 3), i < j → s (i, j) = 1) :
    { e : Sym2 (Fin 3) | ∃ i j, i < j ∧ e = s(i, j) ∧ s (i, j) = 1 } = K3.edgeSet := by
  ext e
  constructor
  · intro h
    obtain ⟨i, j, hij, rfl, _⟩ := h
    simp [K3, hij.ne]
  · intro he
    simp [K3] at he
    induction e using Sym2.inductionOn
    case h i j =>
      simp at he
      by_cases h_lt : i < j
      · use i, j
        -- Provide proofs for: i < j, e = s(i, j), and slack value
        exact ⟨h_lt, rfl, h_s i j h_lt⟩
      · have h_gt : j < i := by
          apply lt_of_le_of_ne (le_of_not_gt h_lt) (ne_comm.mp he)
        use j, i
        -- Sym2.eq_swap handles {i, j} = {j, i}
        exact ⟨h_gt, Sym2.eq_swap, h_s j i h_gt⟩
