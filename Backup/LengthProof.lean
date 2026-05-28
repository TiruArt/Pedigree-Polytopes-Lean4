import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Finset

theorem card_removed_two {n i j : ℕ} (h_n : n ≥ 4)
  (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n) (hij : i ≠ j) :
  (Finset.Icc 1 n \ {i, j}).card = n - 2 := by
  -- 1. Create the set S = {1, ..., n}
  let S := Finset.Icc 1 n

  -- 2. Use card_diff_singleton to remove i, then use it again for j
  -- Need to show i is in S and j is in S
  have h1 : i ∈ S := hi
  have h2 : j ∈ S \ {i} := by
    rw [mem_sdiff, mem_singleton]
    constructor
    · exact hj
    · exact hij

  -- 3. Perform the card reduction
  rw [← card_singleton i] at *
  rw [← sdiff_sdiff] -- S \ {i, j} is S \ {i} \ {j}
  rw [card_sdiff h2]
  rw [card_sdiff h1]

  -- 4. Calculate cardinality of S
  rw [card_Icc]

  -- 5. Final arithmetic (requires n ≥ 2, which is implied by n ≥ 4)
  -- The mathlib card_Icc sets this up for simple arithmetic
  simp only [add_tsub_cancel_left, tsub_add_eq_add_tsub, add_tsub_cancel_right]
  -- Final steps might need specific n-2 rearranging based on your goal
  sorry
