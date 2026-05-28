-- File No. 6 - N_SlackComputation.lean
--
-- MIR slack computation: U^{(k)}(t) for each layer k and edge t.
--
-- From the arXiv paper (Problem MI(l), recursive structure):
--   U^{(l-1)}(p) - A^{(l)} x_l(p) = U^{(l)}(p),  4 ≤ l ≤ n
-- i.e. U^{(k)}(t) = U^{(k-1)}(t) - (A^{(k)} · P)(t)
--
-- Base case: U^{(3)}(t) = 1 for all t (initial capacity = 1).
-- Recursive case (k = k'+4):
--   Old edge (t.j + 1 < k): U^{(k)}(t) = U^{(k-1)}(t.i, t.j, k-1) - A_P
--   New edge (t.j + 1 = k): U^{(k)}(t) = 0 - A_P
--     (edge (t.i, t.j) not yet available before layer k)
--
-- Pattern k'+4 avoids omega failures on Nat.sub in recursive bounds.
--
-- Reference: Arthanari, T.S. arXiv:2507.09069v1 [math.CO].

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_MatrixOps

namespace MembershipProject.Core

open Nat

-- ============================================================
-- MIR STRUCTURE
-- Bundles the generation vectors P_k and their validity conditions:
--   nonneg      : P_k(t) ≥ 0 for all valid triples t
--   new_edge_bal: (A^{(k)} · P_k)(t) = 0 for new edges
--                 (a new edge has no prior flow to balance)
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
-- U^{(k)}(t) = available slack of edge (t.i, t.j) at layer k.
-- Pattern k'+4 makes recursive bounds syntactically clear to Lean.
-- ============================================================

noncomputable def computeSlack (n : ℕ) (mir : MIRStructure n) :
    ∀ (k : ℕ), 3 ≤ k → k ≤ n → Triple → ℚ
  | 3,      _,   _,   _ => 1
  | k' + 4, hk3, hkn, t =>
    let A_P := sparseMatVecMul (k' + 4) ⟨hk3⟩ (mir.P (k' + 4) hk3 hkn) t
    if t.j + 1 < k' + 4 then
      -- old edge: subtract flow used at this layer
      computeSlack n mir (k' + 3) (by omega) (by omega) (t.i, t.j, k' + 3) - A_P
    else
      -- new edge: first appearance, prior slack = 0
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
-- FLOW BOUNDED
-- y_k(t) ≤ U^{(k-1)}(t) for old edges:
-- the flow inserted at layer k cannot exceed the available slack.
-- ============================================================

def FlowBounded (n : ℕ) (mir : MIRStructure n) : Prop :=
  ∀ k' (hkn : k' + 4 ≤ n) (t : Triple),
    t ∈ Delta (k' + 4) → t.j + 1 < k' + 4 →
    sparseMatVecMul (k' + 4) ⟨by omega⟩ (mir.P (k' + 4) (by omega) hkn) t ≤
    computeSlack n mir (k' + 3) (by omega) (by omega) (t.i, t.j, k' + 3)

-- ============================================================
-- NON-NEGATIVITY: U^{(k)}(t) ≥ 0
-- Proved by fuel induction, allowing the IH to be applied
-- to (t.i, t.j, k'+3) rather than t directly.
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
            (mem_Delta_i1 ht) (mem_Delta_ij ht)
            (by have := mem_Delta_jl ht; omega)
        have hprev := ih (k' + 3) (by omega) (by omega) (by omega)
                        (t.i, t.j, k' + 3) ht_prev
        have hbound := hfb k' hkn' t ht hold
        linarith
      · simp only [hold, ↓reduceIte]
        have hjk : t.j + 1 = k' + 4 := by
          have := mem_Delta_jlt ht; omega
        have hbal := mir.new_edge_bal (k' + 4) (by omega) hkn' t ht hjk
        linarith [hbal.symm.le]

/-- The available slack U^{(k)}(t) is non-negative for all valid
    triples t, provided FlowBounded holds (flow ≤ available slack).
    Proof by fuel induction on k. -/
theorem computeSlack_nonneg (n : ℕ) (mir : MIRStructure n)
    (hfb : FlowBounded n mir)
    (k : ℕ) (hk3 : 3 ≤ k) (hkn : k ≤ n) (t : Triple) (ht : t ∈ Delta k) :
    computeSlack n mir k hk3 hkn t ≥ 0 :=
  computeSlack_nonneg_fuel n mir hfb k k le_rfl hk3 hkn t ht

end MembershipProject.Core
