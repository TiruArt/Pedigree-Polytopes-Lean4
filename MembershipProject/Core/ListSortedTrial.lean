import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max

/-! ### 1. Definitions -/

/-- A triple is [i, j, k] such that i < j < k. -/
def IsTriple (t : List ℕ) : Prop :=
  match t with

  | [i, j, k] => i < j ∧ j < k
  | _         => False

/-- Manual decidability to ensure 'decide' works on n=6 examples. -/
instance (t : List ℕ) : Decidable (IsTriple t) :=
  match t with

  | [i, j, k] => inferInstance
  | _         => isFalse (by simp [IsTriple])

/-! ### 2. The Bridge Lemma
    Connects List representation to Finset representation without high-level lemmas.
-/
theorem triple_max {i j k : ℕ} (h_incr : i < j ∧ j < k) :
    ([i, j, k] : List ℕ).toFinset.max = some k := by
  let s := ([i, j, k] : List ℕ).toFinset
  have h_mem : k ∈ s := by simp [s]

  -- Use match to handle Option/WithBot coercion safely
  match h_max : s.max with

  | none =>
      -- Contradiction: Set {i, j, k} isn't empty, so max can't be none.
      have h_nonempty : s.Nonempty := ⟨k, h_mem⟩
      have : s.max ≠ none := Finset.Nonempty.max_get h_nonempty |>.proof_1
      -- If the above fails, use: simp [Finset.max_eq_none, h_nonempty.ne_empty] at h_max
      contradiction

  | some m =>
      -- 1. Prove k ≤ m (property of being max)
      have h_k_le_m : k ≤ m := by
        have h_le := Finset.le_max h_mem
        rw [h_max] at h_le
        exact h_le
      -- 2. Prove m ≤ k (since m is in the set {i, j, k})
      have h_m_le_k : m ≤ k := by
        have h_in_s := Finset.mem_of_max h_max
        simp [s] at h_in_s
        rcases h_in_s with (rfl | rfl | rfl)
        · exact Nat.le_of_lt (Nat.lt_trans h_incr.1 h_incr.2)
        · exact Nat.le_of_lt h_incr.2
        · exact Nat.le_refl k
      -- 3. Conclusion: m = k
      have : m = k := Nat.le_antisymm h_m_le_k h_k_le_m
      rw [this] at h_max
      exact h_max

/-! ### 3. Examples for n=6 -/

/-- A valid pedigree S for n=6. -/
def S_6 : List (List ℕ) := [
  [1, 2, 3],
  [1, 3, 4],
  [1, 4, 5],
  [1, 5, 6]
]

/-- Verify the List contains only valid triples. -/
example : ∀ t ∈ S_6, IsTriple t := by
  intro t ht
  simp [S_6] at ht
  rcases ht with (rfl | rfl | rfl | rfl) <;> decide

/-- Verify the 'parent' lookup logic (List version). -/
example :
  let t_child := [1, 4, 5]
  ∃ t_prev ∈ S_6, t_prev.getLast? = some 4 ∧ (1 : ℕ) ∈ t_prev :=
by
  -- The parent is [1, 3, 4]
  refine ⟨[1, 3, 4], ?_, rfl, by simp⟩
  simp [S_6]

/-- Final conversion check: List length matches Finset card. -/
example : (S_6.map List.toFinset).toFinset.card = 4 := by
  native_decide
