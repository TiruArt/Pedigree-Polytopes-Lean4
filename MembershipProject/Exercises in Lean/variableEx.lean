-- As a theorem with explicit parameter
theorem example_simple (a : Nat) : (a = 1) ∨ (a = 2) → a ≤ 2 := by
  intro h  -- Assume (a=1) ∨ (a=2)
  rcases h with (h1 | h2)
  · -- Case a = 1
    rw [h1]
    omega
  · -- Case a = 2
    rw [h2]
    omega

-- Test it:
example : (1 = 1) ∨ (1 = 2) → 1 ≤ 2 := example_simple 1
theorem example_not_simple (a : Nat) : (a = 1) ∨ (a = 2) → a ≤ 4 := by
  intro h  -- Assume (a=1) ∨ (a=2)
  rcases h with (h1 | h2)
  · -- Case a = 1
    rw [h1]
    omega
  · -- Case a = 2
    rw [h2]
    omega
-- Test it:
example : (1 = 1) ∨ (1 = 2) → 1 ≤ 4 := by
  exact example_not_simple 1
example : (2 = 1) ∨ (2 = 2) → 2 ≤ 4 := by
  exact example_not_simple 2
