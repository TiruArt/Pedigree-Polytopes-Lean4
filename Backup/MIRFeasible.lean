-- Core/MIRFeasible.lean
-- ========================================================
-- MIRStructure to MIRFeasible Conversion
-- Paper: "A Strongly Polynomial Algorithm for Membership
--        in the Pedigree Polytope" by Tiru Arthanari
-- Section 3: MI-Relaxation and Lemma 5
-- ========================================================

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import MembershipProject.Core.Types
import MembershipProject.Core.Basic
import MembershipProject.Core.MatrixOps
import MembershipProject.Core.SlackComputation
import MembershipProject.Core.PedigreeMembershipCharacterisation

set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace MembershipProject.Core

open Nat

-- ============================================================================
-- SECTION 5a: EDGE BRIDGE
-- ============================================================================

section EdgeBridge

def Edge.toPair {k : ℕ} (e : Edge k) : ℕ × ℕ := (e.i, e.j)

def toEdge (k : ℕ) (p : ℕ × ℕ) : Option (Edge k) :=
  if h : p.1 < p.2 ∧ p.2 < k then
    some ⟨p.1, p.2, Nat.lt_trans h.1 h.2, h.2, h.1⟩
  else none

lemma toEdge_toPair {k : ℕ} (e : Edge k) : toEdge k e.toPair = some e := by
  simp only [toEdge, Edge.toPair]
  rw [dif_pos ⟨e.hij, e.hj⟩]

lemma toEdge_none_iff (k : ℕ) (p : ℕ × ℕ) :
    toEdge k p = none ↔ ¬(p.1 < p.2 ∧ p.2 < k) := by
  simp only [toEdge]; split_ifs with h <;> simp [h]

end EdgeBridge

-- ============================================================================
-- SECTION 5b: LIFTING SlackVector AND FLOW
-- ============================================================================

section SlackLift

def liftSlack (n : ℕ)
    (S : ∀ k, 3 ≤ k → k ≤ n → SlackVector k) :
    ℕ → ℕ × ℕ → ℚ :=
  fun m p =>
    let k := m + 3
    if hkn : k ≤ n then
      match toEdge k p with
      | some e => S k (by omega) hkn e
      | none   => 0
    else 0

def liftFlow (n : ℕ) (mir : MIRStructure n) :
    ℕ → ℕ × ℕ → ℚ :=
  fun k p =>
    if hkn : k ≤ n then
      if hk3 : 3 ≤ k then
        match toEdge k p with
        | some e =>
          if e.j + 1 = k then 0
          else sparseMatVecMul k ⟨hk3⟩ (mir.P k hk3 hkn) e
        | none => 0
      else 0
    else 0

end SlackLift

-- ============================================================================
-- SECTION 5c: MIRStructure → MIRFeasible
-- ============================================================================

section MIRStructureToFeasible

private lemma edge_ext (k : ℕ) (e e' : Edge k)
    (hi : e.i = e'.i) (hj : e.j = e'.j) : e = e' := by
  cases e; cases e'
  simp only at hi hj; subst hi; subst hj
  simp [Subsingleton.elim]

private lemma sparseMatVecMul_old_eq (k : Nat) (hk : k ≥ 3)
    (P : GenVector k) (e : Edge k) (h_old : ¬(e.j + 1 = k)) :
    sparseMatVecMul k ⟨hk⟩ P e = P ⟨e.i, e.j, e.hi, e.hj, e.hij⟩ := by
  unfold sparseMatVecMul sparseMatVecMulDirect
  simp only [dif_neg h_old, dif_pos e.hi, dif_pos e.hj, dif_pos e.hij, ↓reduceIte]

noncomputable def MIRStructure.toMIRFeasible {n : ℕ} (mir : MIRStructure n)
    (hn : 4 ≤ n) (hfb : FlowBounded n mir) : MIRFeasible n where

  u := liftSlack n (fun k hk3 hkn => computeSlackSparse n mir k hk3 hkn)
  x := liftFlow n mir
  h_n := hn

  -- ── u_rec ────────────────────────────────────────────────────────────────
  u_rec := by
    intro m hm p
    unfold liftSlack liftFlow
    have hm4n : m + 4 ≤ n := hm
    have hm3n : m + 3 ≤ n := by omega
    simp only [show (m + 1) + 3 = m + 4 from by omega,
               dif_pos hm4n, dif_pos hm3n,
               dif_pos (show (3 : ℕ) ≤ m + 4 from by omega)]
    by_cases hv4 : p.1 < p.2 ∧ p.2 < m + 4
    · rw [show toEdge (m + 4) p =
            some ⟨p.1, p.2, Nat.lt_trans hv4.1 hv4.2, hv4.2, hv4.1⟩ from by
          simp [toEdge, dif_pos hv4]]
      by_cases hv3 : p.2 < m + 3
      · -- ── OLD EDGE ───────────────────────────────────────────────────────
        have hv3' : p.1 < p.2 ∧ p.2 < m + 3 := ⟨hv4.1, hv3⟩
        rw [show toEdge (m + 3) p =
              some ⟨p.1, p.2, Nat.lt_trans hv3'.1 hv3'.2, hv3'.2, hv3'.1⟩ from by
            simp [toEdge, dif_pos hv3']]
        set e4 : Edge (m + 4) :=
          ⟨p.1, p.2, Nat.lt_trans hv4.1 hv4.2, hv4.2, hv4.1⟩
        set e3 : Edge (m + 3) :=
          ⟨p.1, p.2, Nat.lt_trans hv3'.1 hv3'.2, hv3'.2, hv3'.1⟩
        have hOld    : e4.j < (m + 4) - 1  := by simp only [e4]; omega
        have hnotNew : ¬(e4.j + 1 = m + 4) := by simp only [e4]; omega
        simp only [if_neg hnotNew]
        have hrec := computeSlackSparse_old_edge n mir (m + 4) (by omega) hm4n e4 hOld
        have heprev :
            (⟨e4.i, e4.j, show e4.i < m + 3 from by simp only [e4]; omega,
              hOld, e4.hij⟩ : Edge (m + 3)) = e3 :=
          edge_ext (m + 3) _ e3 rfl rfl
        have hrec_clean :
            computeSlackSparse n mir (m + 4) (by omega) hm4n e4 =
            computeSlackSparse n mir (m + 3) (by omega) hm3n e3 -
            sparseMatVecMul (m + 4) ⟨by omega⟩ (mir.P (m + 4) (by omega) hm4n) e4 := by
          convert hrec using 2
        linarith [hrec_clean]
      · -- ── NEW EDGE ───────────────────────────────────────────────────────
        have hnotv3 : ¬(p.1 < p.2 ∧ p.2 < m + 3) := by omega
        rw [show toEdge (m + 3) p = none from
            (toEdge_none_iff (m + 3) p).mpr hnotv3]
        set e4 : Edge (m + 4) :=
          ⟨p.1, p.2, Nat.lt_trans hv4.1 hv4.2, hv4.2, hv4.1⟩
        have hNew  : e4.j + 1 = m + 4   := by simp only [e4]; omega
        have hNewJ : e4.j = (m + 4) - 1 := by omega
        simp only [if_pos hNew, add_zero]
        rw [computeSlackSparse_new_edge n mir (m + 4) (by omega) hm4n e4 hNewJ]
        have hbal := mir.new_edge_balance (m + 4) (by omega) hm4n e4 hNewJ
        linarith
    · -- ── INVALID ────────────────────────────────────────────────────────
      have h4none : toEdge (m + 4) p = none :=
        (toEdge_none_iff (m + 4) p).mpr hv4
      have h3none : toEdge (m + 3) p = none :=
        (toEdge_none_iff (m + 3) p).mpr (fun h => hv4 ⟨h.1, by omega⟩)
      rw [h4none, h3none]
      simp

  -- ── x_nn ─────────────────────────────────────────────────────────────────
  x_nn := by
    intro k p
    unfold liftFlow
    by_cases hkn : k ≤ n
    · by_cases hk3 : 3 ≤ k
      · simp only [dif_pos hkn, dif_pos hk3]
        rcases toEdge k p with _ | e
        · norm_num
        · by_cases hnew : e.j + 1 = k
          · simp [hnew]
          · simp only [if_neg hnew]
            rw [sparseMatVecMul_old_eq k hk3 (mir.P k hk3 hkn) e hnew]
            exact mir.nonneg k hk3 hkn ⟨e.i, e.j, e.hi, e.hj, e.hij⟩
      · simp [dif_neg hk3]
    · simp [dif_neg hkn]

  -- ── u_nn ─────────────────────────────────────────────────────────────────
  u_nn := by
    intro m p
    unfold liftSlack
    by_cases hkn : m + 3 ≤ n
    · simp only [dif_pos hkn]
      rcases toEdge (m + 3) p with _ | e
      · norm_num
      · apply computeSlackSparse_nonneg n mir hfb (m + 3) (by omega) hkn e
    · simp only [dif_neg hkn]; norm_num

  -- ── u0_le1 ───────────────────────────────────────────────────────────────
  u0_le1 := by
    intro p
    unfold liftSlack
    simp only [show (0 : ℕ) + 3 = 3 from rfl,
               dif_pos (show 3 ≤ n from by omega)]
    rcases toEdge 3 p with _ | e
    · norm_num
    · have hbase := computeSlackSparse_base_case n mir (by omega) e
      simp only [initialSlack] at hbase
      linarith

end MIRStructureToFeasible

end MembershipProject.Core
