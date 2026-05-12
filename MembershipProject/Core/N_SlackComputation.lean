-- Core/N_SlackComputation.lean
-- MIR slack computation. Triple = ℕ × ℕ × ℕ.

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_MatrixOps

namespace MembershipProject.Core

open Nat

-- ============================================================
-- MIR STRUCTURE
-- ============================================================

structure MIRStructure (n : ℕ) where
  P            : ∀ (k : ℕ), 3 ≤ k → k ≤ n → GenVector k
  nonneg       : ∀ k (hk3 : 3 ≤ k) (hkn : k ≤ n) (t : Triple),
                   t ∈ Delta k → P k hk3 hkn t ≥ 0
  new_edge_bal : ∀ k (hk : 4 ≤ k) (hkn : k ≤ n) (t : Triple),
                   t ∈ Delta k → t.j + 1 = k →
                   sparseMatVecMul k ⟨by omega⟩ (P k (by omega) hkn) t = 0

-- ============================================================
-- SLACK COMPUTATION
-- Pattern on 3 and k'+4 so recursive bounds are syntactically clear.
-- ============================================================

noncomputable def computeSlack (n : ℕ) (mir : MIRStructure n) :
    ∀ (k : ℕ), 3 ≤ k → k ≤ n → Triple → ℚ
  | 3,      _,   _,   _ => 1
  | k' + 4, hk3, hkn, t =>
    let A_P := sparseMatVecMul (k' + 4) ⟨hk3⟩ (mir.P (k' + 4) hk3 hkn) t
    if t.j + 1 < k' + 4 then
      computeSlack n mir (k' + 3) (by omega) (by omega) (t.i, t.j, k' + 3) - A_P
    else
      0 - A_P

-- ============================================================
-- STEP LEMMAS (definitional, proved by rfl)
-- ============================================================

lemma computeSlack_base (n : ℕ) (mir : MIRStructure n)
    (hkn : 3 ≤ n) (t : Triple) :
    computeSlack n mir 3 (by omega) hkn t = 1 := rfl

lemma computeSlack_step (n : ℕ) (mir : MIRStructure n)
    (k' : ℕ) (hk3 : 3 ≤ k' + 4) (hkn : k' + 4 ≤ n) (t : Triple) :
    computeSlack n mir (k' + 4) hk3 hkn t =
    let A_P := sparseMatVecMul (k' + 4) ⟨hk3⟩ (mir.P (k' + 4) hk3 hkn) t
    if t.j + 1 < k' + 4 then
      computeSlack n mir (k' + 3) (by omega) (by omega) (t.i, t.j, k' + 3) - A_P
    else
      0 - A_P := rfl

-- ============================================================
-- FLOW BOUNDED: y_k(t) ≤ U^(k-1)(t) for old edges
-- Stated with k'+4 to match computeSlack pattern.
-- ============================================================

def FlowBounded (n : ℕ) (mir : MIRStructure n) : Prop :=
  ∀ k' (hkn : k' + 4 ≤ n) (t : Triple),
    t ∈ Delta (k' + 4) → t.j + 1 < k' + 4 →
    sparseMatVecMul (k' + 4) ⟨by omega⟩ (mir.P (k' + 4) (by omega) hkn) t ≤
    computeSlack n mir (k' + 3) (by omega) (by omega) (t.i, t.j, k' + 3)

-- ============================================================
-- NON-NEGATIVITY via fuel induction
-- Fuel lets us apply IH to (t.i, t.j, k'+3) not just t.
-- ============================================================

private lemma computeSlack_nonneg_fuel (n : ℕ) (mir : MIRStructure n)
    (hfb : FlowBounded n mir) :
    ∀ (fuel k : ℕ), k ≤ fuel → ∀ (hk3 : 3 ≤ k) (hkn : k ≤ n)
    (t : Triple), t ∈ Delta k →
    computeSlack n mir k hk3 hkn t ≥ 0 := by
  intro fuel
  induction fuel with
  | zero => intro k hkf; omega
  | succ f ih =>
    intro k hkf hk3 hkn t ht
    match k, hk3, hkn with
    | 3, _, _ =>
      rw [computeSlack_base]; norm_num
    | k' + 4, hk3', hkn' =>
      rw [computeSlack_step]
      simp only
      by_cases hold : t.j + 1 < k' + 4
      · simp only [hold, ↓reduceIte]
        have ht_prev : (t.i, t.j, k' + 3) ∈ Delta (k' + 3) :=
          mem_Delta_self t.i t.j
            (mem_Delta_i1 ht) (mem_Delta_ij ht) (by have := mem_Delta_jl ht; omega)
        have hprev := ih (k' + 3) (by omega) (by omega) (by omega)
                        (t.i, t.j, k' + 3) ht_prev
        have hbound := hfb k' hkn' t ht hold
        linarith
      · simp only [hold, ↓reduceIte]
        have hjk : t.j + 1 = k' + 4 := by
          have := mem_Delta_jlt ht; omega
        have hbal := mir.new_edge_bal (k' + 4) (by omega) hkn' t ht hjk
        linarith [hbal.symm.le]

theorem computeSlack_nonneg (n : ℕ) (mir : MIRStructure n)
    (hfb : FlowBounded n mir)
    (k : ℕ) (hk3 : 3 ≤ k) (hkn : k ≤ n) (t : Triple) (ht : t ∈ Delta k) :
    computeSlack n mir k hk3 hkn t ≥ 0 :=
  computeSlack_nonneg_fuel n mir hfb k k le_rfl hk3 hkn t ht

end MembershipProject.Core
