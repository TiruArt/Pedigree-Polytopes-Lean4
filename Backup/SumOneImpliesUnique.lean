import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

open List

theorem only_one_is_one {L : List ℕ}
  (h_binary : ∀ x ∈ L, x = 0 ∨ x = 1)
  (h_sum : L.sum = 1) :
  ∃! i : Fin L.length, L[i] = 1 := by
  induction L with


  | nil =>
    simp at h_sum
  | cons x xs ih =>
    simp only [sum_cons] at h_sum
    have hx : x = 0 ∨ x = 1 := h_binary x (by simp)
    have hxs : ∀ y ∈ xs, y = 0 ∨ y = 1 := fun y hy => h_binary y (by simp [hy])
    cases hx with


    | inl h0 =>
      rw [h0, Nat.zero_add] at h_sum
      specialize ih hxs h_sum
      rcases ih with ⟨i, hi, h_uniq⟩
      refine ⟨i.succ, hi, ?_⟩
      intro j hj
      cases j using Fin.cases with
      | zero =>
        simp [h0] at hj

      | succ j =>
        apply congr_arg Fin.succ
        apply h_uniq
        simp at hj
        exact hj

    | inr h1 =>
      rw [h1, Nat.add_comm] at h_sum
      have h_xs_sum : xs.sum = 0 := Nat.add_right_cancel h_sum
      refine ⟨0, by simp [h1], ?_⟩
      intro j hj
      cases j using Fin.cases with


      | zero => rfl
      | succ j =>
        -- Define a dedicated local function to handle the "sum 0 -> elements 0" proof
        let rec all_zero {ls : List ℕ} (h_zero : ls.sum = 0) (k : Fin ls.length) : ls[k] = 0 :=
          match ls, k with

          | y :: ys, ⟨0, _⟩ => (Nat.add_eq_zero_iff.mp h_zero).left
          | y :: ys, ⟨k+1, hk⟩ => all_zero (Nat.add_eq_zero_iff.mp h_zero).right ⟨k, Nat.lt_of_succ_lt_succ hk⟩

        simp at hj
        have h_val_is_zero := all_zero h_xs_sum j
        -- Contradict hj (1) with h_val_is_zero (0)
        have h_one_eq_zero : 1 = 0 := hj.symm.trans h_val_is_zero
        exact Nat.noConfusion h_one_eq_zero
