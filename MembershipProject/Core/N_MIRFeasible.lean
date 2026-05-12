-- Core/N_MIRFeasible.lean
-- Bridge: MIRStructure → MIRFeasible.

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_Types
import MembershipProject.Core.N_MatrixOps
import MembershipProject.Core.N_SlackComputation

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MembershipProject.Core

open Nat

-- ============================================================
-- BRIDGE: ℕ × ℕ → Option Triple at layer k
-- ============================================================

def toTriple (k : ℕ) (p : ℕ × ℕ) : Option Triple :=
  if h : 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < k then some (p.1, p.2, k) else none

lemma toTriple_mem {k : ℕ} {p : ℕ × ℕ} {t : Triple}
    (h : toTriple k p = some t) : t ∈ Delta k := by
  simp only [toTriple] at h
  by_cases hv : 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < k
  · rw [dif_pos hv] at h; simp only [Option.some.injEq] at h; subst h
    exact mem_Delta_self p.1 p.2 hv.1 hv.2.1 hv.2.2
  · rw [dif_neg hv] at h; simp at h

lemma toTriple_eq {k : ℕ} {p : ℕ × ℕ} {t : Triple}
    (h : toTriple k p = some t) : t = (p.1, p.2, k) := by
  simp only [toTriple] at h
  by_cases hv : 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < k
  · rw [dif_pos hv] at h; simp only [Option.some.injEq] at h; exact h.symm
  · rw [dif_neg hv] at h; simp at h

lemma toTriple_none_iff {k : ℕ} {p : ℕ × ℕ} :
    toTriple k p = none ↔ ¬(1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < k) := by
  simp only [toTriple]
  by_cases hv : 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < k
  · simp [dif_pos hv, hv]
  · simp [dif_neg hv, hv]

-- ============================================================
-- LIFTING
-- liftSlack m p = U^(m+3)(p)
-- liftFlow  k p = y_k(p)   [k is the layer directly]
-- ============================================================

noncomputable def liftSlack (n : ℕ)
    (S : ∀ k, 3 ≤ k → k ≤ n → Triple → ℚ) : ℕ → ℕ × ℕ → ℚ :=
  fun m p =>
    if hkn : m + 3 ≤ n then
      match toTriple (m + 3) p with
      | some t => S (m + 3) (by omega) hkn t
      | none   => 0
    else 0

-- liftFlow k p = y_k(p): generation value at layer k
noncomputable def liftFlow (n : ℕ) (mir : MIRStructure n) : ℕ → ℕ × ℕ → ℚ :=
  fun k p =>
    if hkn : k ≤ n then
      if hk3 : 3 ≤ k then
        match toTriple k p with
        | some t =>
          if t.j + 1 = k then 0
          else sparseMatVecMul k ⟨hk3⟩ (mir.P k hk3 hkn) t
        | none => 0
      else 0
    else 0

-- ============================================================
-- MIRStructure → MIRFeasible
-- u_rec: liftSlack (m+1) p + liftFlow (m+4) p = liftSlack m p
--   i.e. U^(m+4)(p) + y_(m+4)(p) = U^(m+3)(p)
--   which is exactly computeSlack_step rearranged.
-- ============================================================

noncomputable def MIRStructure.toMIRFeasible {n : ℕ} (mir : MIRStructure n)
    (hn : 4 ≤ n) (hfb : FlowBounded n mir) : MIRFeasible n where
  u   := liftSlack n (computeSlack n mir)
  x   := liftFlow n mir
  h_n := hn

  u_rec := by
    intro m hm p
    simp only [liftSlack, liftFlow, show m + 1 + 3 = m + 4 from by omega]
    have hm3 : m + 3 ≤ n := by omega
    have hm4 : m + 4 ≤ n := hm
    simp only [dif_pos hm4, dif_pos hm3, dif_pos (show 3 ≤ m + 4 from by omega)]
    -- case split on toTriple (m+4) p
    rcases h4 : toTriple (m + 4) p with _ | t4
    · -- t4 = none: U^(m+4) = 0, y_(m+4) = 0, U^(m+3) must = 0
      simp only [h4]
      -- t3 must also be none (p.2 ≥ m+4 > m+3)
      have hn4 := toTriple_none_iff.mp h4
      have hn3 : toTriple (m + 3) p = none := by
        rw [toTriple_none_iff]; push_neg at hn4 ⊢; intro h1 h2; omega
      simp only [hn3]; ring
    · -- t4 exists
      have ht4 := toTriple_mem h4
      have ht4_eq := toTriple_eq h4
      simp only [h4]
      rcases h3 : toTriple (m + 3) p with _ | t3
      · -- t4 exists, t3 = none → new edge
        simp only [h3]
        have hn3 := toTriple_none_iff.mp h3
        push_neg at hn3
        -- extract p.1 = t4.i, p.2 = t4.j from ht4_eq
        have hi1 : 1 ≤ p.1 := by
          have := mem_Delta_i1 ht4; rw [ht4_eq] at this; simpa [Triple.i] using this
        have hij : p.1 < p.2 := by
          have := mem_Delta_ij ht4; rw [ht4_eq] at this; simpa [Triple.i, Triple.j] using this
        have hj := mem_Delta_jl ht4
        rw [ht4_eq] at hj; simp [Triple.j] at hj
        have hge := hn3 hi1 hij  -- p.2 ≥ m + 3
        have hnew : t4.j + 1 = m + 4 := by
          rw [ht4_eq]; simp [Triple.j]; omega
        simp only [hnew, ↓reduceIte]
        rw [computeSlack_step]
        simp only [hnew, show ¬(t4.j + 1 < m + 4) from by omega, ↓reduceIte]
        have hbal := mir.new_edge_bal (m + 4) (by omega) hm4 t4 ht4 hnew
        simp only [hbal, show ¬(m + 4 < m + 4) from by omega, ↓reduceIte,
                   sub_zero, zero_sub, add_zero]
      · -- Both exist: old edge
        have ht3 := toTriple_mem h3
        have ht3_eq := toTriple_eq h3
        -- t3 = (p.1, p.2, m+3) = (t4.i, t4.j, m+3)
        have hpq : p.1 = t4.i ∧ p.2 = t4.j := by
          rw [ht4_eq]; simp [Triple.i, Triple.j]
        have hold : t4.j + 1 < m + 4 := by
          have := mem_Delta_jl ht3
          rw [ht3_eq] at this; simp [Triple.j] at this
          rw [ht4_eq]; simp [Triple.j]; omega
        have ht3_val : t3 = (t4.i, t4.j, m + 3) := by
          rw [ht3_eq, hpq.1, hpq.2]
        simp only [show ¬(t4.j + 1 = m + 4) from by omega, ↓reduceIte, h3]
        rw [computeSlack_step, ht3_val]
        simp only [hold, ↓reduceIte]
        ring

  x_nn := by
    intro k p; simp only [liftFlow]
    by_cases hkn : k ≤ n
    · simp only [dif_pos hkn]
      by_cases hk3 : 3 ≤ k
      · simp only [dif_pos hk3]
        rcases h : toTriple k p with _ | t
        · norm_num
        · simp only
          split_ifs with hnew
          · norm_num
          · -- sparseMatVecMul k P t = P (t.i, t.j, k) (old edge)
            rw [sparseMatVecMul_old k ⟨hk3⟩ (mir.P k hk3 hkn) t hnew]
            have hteq : t = (t.i, t.j, k) := by
              obtain ⟨ti, tj, tk⟩ := t
              have := mem_Delta_k (toTriple_mem h)
              simp [Triple.i, Triple.j, Triple.k] at this ⊢; exact this
            rw [← hteq]
            linarith [mir.nonneg k hk3 hkn t (toTriple_mem h)]
      · simp [dif_neg hk3]
    · simp [dif_neg hkn]

  u_nn := by
    intro m p; simp only [liftSlack]
    by_cases hkn : m + 3 ≤ n
    · simp only [dif_pos hkn]
      rcases h : toTriple (m + 3) p with _ | t
      · norm_num
      · exact computeSlack_nonneg n mir hfb (m + 3) (by omega) hkn t
            (toTriple_mem h)
    · simp [dif_neg hkn]

  u0_le1 := by
    intro p; simp only [liftSlack, show 0 + 3 = 3 from rfl]
    by_cases hkn : 3 ≤ n
    · simp only [dif_pos hkn]
      rcases h : toTriple 3 p with _ | t
      · norm_num
      · simp only [computeSlack_base]; norm_num
    · simp [dif_neg hkn]

end MembershipProject.Core
