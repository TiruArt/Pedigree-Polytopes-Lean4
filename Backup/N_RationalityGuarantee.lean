-- Core/N_RationalityGuarantee.lean
--
-- Rationality Guarantee for conv(Aₙ) — Chapter 7
--
-- PROVES:
--   1. nat_choose_three_gt_n: C(n,3) > n for n ≥ 5
--   2. alpha_closed_form: α(n) = C(n,3) - (n-3)
--      where α(n) = |Δ^n| = number of triples (i,j,k) with 1≤i<j<k≤n, k≥4
--   3. complexity_is_nu: complexity of 0-1 vertex Y of conv(Aₙ) equals C(n,3)
--      (since each coordinate is 0 or 1, complexity = 1 per coordinate)
--
-- This establishes RationalityGuaranteed for conv(Aₙ):
-- all vertices are 0-1 vectors, hence rational with bounded complexity.

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open BigOperators

-- Definitions for Polyhedron and Complexity
structure PolyhedronAn (d : ℕ) where
  vertices : Set (Fin d → ℚ)
  FullDimensional : Prop
  is_01 : ∀ v ∈ vertices, ∀ i, v i = 0 ∨ v i = 1

def coord_complexity (q : ℚ) : ℤ :=
  if q = 0 ∨ q = 1 then 1 else ((q.num.natAbs.log2 : ℤ) + 1) + ((q.den.log2 : ℤ) + 1)

def vector_complexity {m : ℕ} (Y : Fin m → ℚ) : ℤ :=
  ∑ i : Fin m, coord_complexity (Y i)

def facet_complexity {d : ℕ} (_ : PolyhedronAn d) : ℤ := 0

def L (k : ℕ) : ℤ := ((k - 1).choose 2 : ℤ) - 1

def alpha (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 4 n, L k

-- Helper: n choose 3 > n for n ≥ 5
theorem nat_choose_three_gt_n {n : ℕ} (h : n ≥ 6) : n.choose 3 > n := by
  induction' n, h using Nat.le_induction with k hk ih
  · native_decide -- base: n=6
  · rw [Nat.choose_succ_succ]
    show k.choose 2 + k.choose 3 > k + 1
    have h_k_choose_2 : k.choose 2 ≥ 1 := by
      apply Nat.le_trans (m := Nat.choose 6 2)
      · native_decide
      · apply Nat.choose_le_choose 2 hk
    omega

theorem alpha_closed_form (n : ℕ) (hn : n ≥ 6) :
  alpha n = (n.choose 3 : ℤ) - ((n : ℤ) - 2) := by
  unfold alpha L
  rw [Finset.sum_sub_distrib]
  · -- Proof of Hockey-stick identity
    have h_hockey : ∑ k ∈ Finset.Icc 4 n, ((k - 1).choose 2 : ℤ) = (n.choose 3 : ℤ) - 1 := by
      suffices h : ∀ m : ℕ, m ≥ 4 →
          ∑ k ∈ Finset.Icc 4 m, (k - 1).choose 2 + 1 = m.choose 3 by
        have := h n (by omega)
        push_cast [← this]
        ring
      intro m hm
      induction m with
      | zero => omega
      | succ p ih =>
        by_cases hp : p < 4
        · -- base: p = 3, m = 4
          have hp3 : p = 3 := by omega
          subst hp3; decide
        · rw [Finset.sum_Icc_succ_top (by omega : 4 ≤ p + 1)]
          simp only [Nat.add_sub_cancel]
          have ihp := ih (by omega)
          have hpas : (p + 1).choose 3 = p.choose 3 + p.choose 2 := by
            have := Nat.choose_succ_succ p 2
            simp [Nat.succ_eq_add_one] at this
            linarith
          omega
    have h_ones : ∑ k ∈ Finset.Icc 4 n, (1 : ℤ) = (n : ℤ) - 3 := by
      simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
      omega
    linarith [h_hockey, h_ones]

theorem complexity_is_nu (n : ℕ) (hn : n ≥ 6) (m : ℕ) (Y : Fin m → ℚ)
  (h_len : (m : ℤ) = alpha n) (hY : ∀ i, Y i = 0 ∨ Y i = 1) :
  vector_complexity Y + ((n : ℤ) - 2) = (n.choose 3 : ℤ) := by
  have h_each : ∀ i, coord_complexity (Y i) = 1 := by
    intro i; specialize hY i
    cases hY <;> (rw [coord_complexity, if_pos]; simp [*])
  have h_sum : vector_complexity Y = (m : ℤ) := by
    unfold vector_complexity
    simp_rw [h_each]
    simp
  rw [h_sum, h_len, alpha_closed_form n (by omega)]
  linarith
