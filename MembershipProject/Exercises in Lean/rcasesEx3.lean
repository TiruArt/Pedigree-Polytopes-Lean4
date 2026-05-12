-- Instead of: rcases h with (h1 | (h2 | h3))
-- Do this:
example {a : Nat} (h : (a = 1) ∨ ((a = 2) ∨ (a = 3))) : a ≤ 3 := by
  rcases h with (h1 | h23)  -- First level
  · rw [h1]; omega
  · rcases h23 with (h2 | h3)  -- Second level
    · rw [h2]; omega
    · rw [h3]; omega
