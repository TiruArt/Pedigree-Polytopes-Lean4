import Mathlib.Data.Nat.Choose.Sum

open Nat
open Finset
open scoped BigOperators

/--
The sum of cardinalities of Delta_k for k from 4 to n is (n choose 3) - 1.
This proof uses induction and handles natural number subtraction constraints.
-/



theorem sum_delta_k_card (n : ℕ) (hn : n ≥ 4) :
    ∑ k ∈ Icc 4 n, (k - 1).choose 2 = n.choose 3 - 1 := by
  induction n, hn using Nat.le_induction with

  | base =>
    simp
  | succ n h' ih =>
    -- 1. Split the sum
    rw [sum_Icc_succ_top (Nat.le_succ_of_le h')]
    rw [ih]
    -- 2. Simplify index
    have h_idx : n + 1 - 1 = n := rfl
    rw [h_idx]

    -- 3. We have: (n.choose 3 - 1) + n.choose 2 = (n + 1).choose 3 - 1
    -- Strategy: Add 1 to both sides to eliminate the -1.
    apply Nat.add_right_cancel (m := 1)

    -- 4. Simplify the RHS: (n + 1).choose 3 - 1 + 1 = (n + 1).choose 3
    rw [Nat.sub_add_cancel]
    · -- 5. Handle the LHS: (n.choose 3 - 1 + n.choose 2) + 1
      -- Rearrange to put the +1 next to the -1
      rw [add_assoc, add_comm (n.choose 2) 1, ← add_assoc]
      rw [Nat.sub_add_cancel]
      · -- Goal: n.choose 3 + n.choose 2 = (n + 1).choose 3
        rw [add_comm, ← choose_succ_succ]
      · -- Prove n.choose 3 ≥ 1
        apply Nat.choose_pos
        exact Nat.le_trans (by decide) h'
    · -- Prove (n+1).choose 3 ≥ 1
      apply Nat.choose_pos
      exact Nat.le_trans (by decide) (Nat.le_succ_of_le h')
