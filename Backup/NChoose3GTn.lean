import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

theorem nat_choose_three_gt_n {n : ℕ} (h : n ≥ 5) : n.choose 3 > n := by
  induction' n, h using Nat.le_induction with k hk ih
  · native_decide
  · rw [Nat.choose_succ_succ]
    -- This line tells Lean to treat (Nat.succ 2) as 3 so it matches 'ih'
    show k.choose 2 + k.choose 3 > k + 1

    have h_k_choose_2 : k.choose 2 ≥ 1 := by
      apply Nat.le_trans (m := Nat.choose 5 2)
      · native_decide
      · apply Nat.choose_le_choose 2 hk

    -- Using 'omega' is best here as it handles Nat inequalities very well
    omega
