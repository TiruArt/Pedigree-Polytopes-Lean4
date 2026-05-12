-- Use Nat instead of ℕ
example {a : Nat } (h : (a = 1) ∨ ((a = 2) ∨ (a = 4))) : (a ≤ 4) := by
  rcases h with (h1 | h24)
  · -- Case: a = 1
    rw [h1]
    omega
  · -- Case: (a = 2) ∨ (a = 4)
    rcases h24 with (h2 | h4)
    · -- Subcase: a = 2
      --rw [h2]
      omega
    · -- Subcase: a = 4
      --rw [h4]
      omega
