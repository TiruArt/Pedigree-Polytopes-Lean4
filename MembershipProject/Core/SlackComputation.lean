-- Core/SlackComputation.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import MembershipProject.Core.Basic
import MembershipProject.Core.MatrixOps
set_option linter.unusedVariables false
namespace MembershipProject.Core

open Nat

-- ============================================
-- INITIAL SLACK
-- ============================================

def initialSlack : SlackVector 3 := fun _ => (1 : Rat)

-- ============================================
-- RECURSIVE MIR STRUCTURE
-- ============================================

/-- Mathematical structure for Sparse Recursive MIR algorithm.
    Three fields:
      P              - generation vector at each layer
      nonneg         - P entries are non-negative
      new_edge_balance - for new arcs (e.j = k-1), the generation
                         row sum is zero (availability constraint) -/
structure MIRStructure (n : Nat) where
  P : ∀ (k : Nat), 3 ≤ k → k ≤ n → GenVector k
  nonneg : ∀ (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n) (v : GenVar k),
    P k hk3 hkn v ≥ (0 : Rat)
  new_edge_balance : ∀ (k : Nat) (hk : 4 ≤ k) (hkn : k ≤ n)
      (e : Edge k) (h_new : e.j = k - 1),
    sparseMatVecMul k ⟨by omega⟩ (P k (by omega) hkn) e = 0

-- ============================================
-- SLACK COMPUTATION
-- ============================================

def computeSlackSparse (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n) : SlackVector k :=
  if h : k = 3 then
    h ▸ initialSlack
  else
    have hk_prev : 3 ≤ k - 1 := by omega
    have hkn_prev : k - 1 ≤ n := by omega
    let U_prev := computeSlackSparse n mir (k - 1) hk_prev hkn_prev
    let A_k : SparseGenerationMatrix k := ⟨hk3⟩
    let P_k := mir.P k hk3 hkn
    fun e =>
      if hj : e.j < k - 1 then
        have hi_prev : e.i < k - 1 := by
          have h1 : e.i < e.j := e.hij
          omega
        let e_prev : Edge (k - 1) := ⟨e.i, e.j, hi_prev, hj, e.hij⟩
        U_prev e_prev - sparseMatVecMul k A_k P_k e
      else
        (0 : Rat) - sparseMatVecMul k A_k P_k e
termination_by k
decreasing_by omega


-- ============================================
-- THEOREMS ABOUT SLACK COMPUTATION
-- ============================================

theorem computeSlackSparse_base_case (n : Nat) (mir : MIRStructure n)
    (hn : n ≥ 3) (e : Edge 3) :
    computeSlackSparse n mir 3 (by omega) (by omega) e = initialSlack e := by
  unfold computeSlackSparse
  simp

theorem computeSlackSparse_old_edge (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk : k ≥ 4) (hkn : k ≤ n) (e : Edge k)
    (h_old : e.j < k - 1) :
    computeSlackSparse n mir k (by omega) hkn e =
    computeSlackSparse n mir (k - 1) (by omega) (by omega : k - 1 ≤ n)
      ⟨e.i, e.j, by have h1 : e.i < e.j := e.hij; omega, h_old, e.hij⟩ -
    sparseMatVecMul k ⟨by omega⟩ (mir.P k (by omega) hkn) e := by
  conv_lhs => unfold computeSlackSparse
  simp [show k ≠ 3 by omega, h_old]

theorem computeSlackSparse_new_edge (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk : k ≥ 4) (hkn : k ≤ n) (e : Edge k)
    (h_new : e.j = k - 1) :
    computeSlackSparse n mir k (by omega) hkn e =
    0 - sparseMatVecMul k ⟨by omega⟩ (mir.P k (by omega) hkn) e := by
  unfold computeSlackSparse
  have h_not_old : ¬(e.j < k - 1) := by omega
  simp only [show k ≠ 3 by omega, ↓reduceDIte, h_not_old, ↓reduceDIte]

theorem computeSlackSparse_correct_base (n : Nat) (mir : MIRStructure n)
    (hn : n ≥ 3) :
    ∀ e : Edge 3,
      computeSlackSparse n mir 3 (by omega) (by omega : 3 ≤ n) e = initialSlack e :=
  fun e => computeSlackSparse_base_case n mir hn e

theorem computeSlackSparse_correct_step_old (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk : k ≥ 4) (hkn : k ≤ n) (edge : Edge k)
    (h_old : edge.j < k - 1) :
    computeSlackSparse n mir k (by omega) hkn edge =
    computeSlackSparse n mir (k - 1) (by omega) (by omega : k - 1 ≤ n)
      ⟨edge.i, edge.j,
       by have h1 : edge.i < edge.j := edge.hij; omega, h_old, edge.hij⟩ -
    sparseMatVecMul k ⟨by omega⟩ (mir.P k (by omega) hkn) edge :=
  computeSlackSparse_old_edge n mir k hk hkn edge h_old

theorem computeSlackSparse_correct_step_new (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk : k ≥ 4) (hkn : k ≤ n) (edge : Edge k)
    (h_new : edge.j ≥ k - 1) :
    computeSlackSparse n mir k (by omega) hkn edge =
    0 - sparseMatVecMul k ⟨by omega⟩ (mir.P k (by omega) hkn) edge := by
  have h_eq : edge.j = k - 1 := by
    have hj : edge.j < k := edge.hj
    omega
  exact computeSlackSparse_new_edge n mir k hk hkn edge h_eq

theorem computeSlackSparse_correct_step (n : Nat) (mir : MIRStructure n)
    (k : Nat) (hk : k ≥ 4) (hkn : k ≤ n) (edge : Edge k) :
    if h : edge.j < k - 1 then
      computeSlackSparse n mir k (by omega) hkn edge =
      computeSlackSparse n mir (k - 1) (by omega) (by omega : k - 1 ≤ n)
        ⟨edge.i, edge.j,
         by have h1 : edge.i < edge.j := edge.hij; omega, h, edge.hij⟩ -
      sparseMatVecMul k ⟨by omega⟩ (mir.P k (by omega) hkn) edge
    else
      computeSlackSparse n mir k (by omega) hkn edge =
      0 - sparseMatVecMul k ⟨by omega⟩ (mir.P k (by omega) hkn) edge := by
  split
  case isTrue h_old =>
    exact computeSlackSparse_old_edge n mir k hk hkn edge h_old
  case isFalse h_new =>
    exact computeSlackSparse_correct_step_new n mir k hk hkn edge (by omega)

-- ============================================
-- SLACK NON-NEGATIVITY
-- ============================================

-- This property cannot be derived from the recurrence alone.
-- It requires the input invariant: at each old-edge step,
-- the previous slack is at least the current flow.
-- This is a validity condition on MIR solutions and is
-- left as a sorry pending a separate inductive argument
-- over the full MIR feasibility conditions.
-- ============================================
-- SLACK NON-NEGATIVITY
-- ============================================

/-- Flow-dominance hypothesis: at each old-edge step, the generation
    vector entry is bounded above by the previous slack.
    This is a validity condition on MIR inputs; it cannot be derived
    from the recurrence definition alone. -/
def FlowBounded (n : Nat) (mir : MIRStructure n) : Prop :=
  ∀ (k : Nat) (hk : 4 ≤ k) (hkn : k ≤ n)
    (e : Edge k) (h_old : e.j < k - 1),
    let hk3'  : 3 ≤ k - 1     := Nat.le_pred_of_lt (Nat.lt_of_succ_le hk)
    let hkn'  : k - 1 ≤ n     := Nat.le_trans (Nat.pred_le k) hkn
    let e_prev : Edge (k - 1) :=
      ⟨e.i, e.j, Nat.lt_trans e.hij h_old, h_old, e.hij⟩
    sparseMatVecMul k ⟨Nat.le_of_succ_le hk⟩
        (mir.P k (Nat.le_of_succ_le hk) hkn) e ≤
    computeSlackSparse n mir (k - 1) hk3' hkn' e_prev
theorem computeSlackSparse_nonneg (n : Nat) (mir : MIRStructure n)
    (h_flow_bound : FlowBounded n mir)
    (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n) (e : Edge k) :
    computeSlackSparse n mir k hk3 hkn e ≥ 0 := by
  by_cases hk3' : k = 3
  · -- base case: slack = 1
    subst hk3'
    have hbase := computeSlackSparse_base_case n mir hkn e
    simp only [initialSlack] at hbase
    linarith
  · have hk4 : 4 ≤ k := by omega
    by_cases hj : e.j < k - 1
    · -- old edge: slack = prev_slack - flow ≥ 0
      have hrec   := computeSlackSparse_old_edge n mir k hk4 hkn e hj
      have hbound := h_flow_bound k hk4 hkn e hj
      linarith
    · -- new edge: e.j = k - 1, flow = 0, slack = 0
      have hj_lt  : e.j < k      := e.hj
      have hj_eq  : e.j = k - 1  := by omega
      have hrec   := computeSlackSparse_new_edge n mir k hk4 hkn e hj_eq
      have hbal   := mir.new_edge_balance k hk4 hkn e hj_eq
      linarith

end MembershipProject.Core
