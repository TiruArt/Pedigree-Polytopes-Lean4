-- Core/Lemma7.lean
-- ========================================================
-- Lemma 7: Y^s ∈ P_MI(k)
-- Paper: "A Strongly Polynomial Algorithm for Membership
--        in the Pedigree Polytope" by Tiru Arthanari
-- Section 6.2, page 27
-- ========================================================

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import MembershipProject.Core.LayeredNetwork
import MembershipProject.Core.MCF
import MembershipProject.Core.MIRelaxation
import MembershipProject.Core.RestrictionFull

namespace MembershipProject.Core

open Finset BigOperators

variable {n k : ℕ} (hk : 4 ≤ k) (hkn : k ≤ n)
variable (X : LayeredPoint n) (net : LayeredNetwork n (k-1))
variable (mcf : MCF (k-1) net) (h_opt : mcf.total_flow = z_max net)

/-- Y^s vector from commodity flows (Equation 33) -/
def Y_vector (s : Commodity (k-1)) (l : ℕ) (e : Edge l) : ℚ :=
  ∑ a ∈ arcs_through_node ⟨l, e⟩, mcf.f_s s a

/-- Total flow of commodity s -/
def v_s (s : Commodity (k-1)) : ℚ :=
  mcf.total_flow_commodity s

/-- Normalized Y = 1/v^s Y^s -/
def Y (s : Commodity (k-1)) (l : ℕ) (e : Edge l) : ℚ :=
  (1 / v_s mcf s) * Y_vector mcf s l e

/-- U^{(3)} base vector -/
def U0 (e : Edge 3) : ℚ :=
  if (e.i = 1 ∧ e.j = 2) ∨ (e.i = 1 ∧ e.j = 3) ∨ (e.i = 2 ∧ e.j = 3) then 1 else 0

/-- Slack variables U^{(l)} defined recursively -/
def U (Y : ∀ l e, ℚ) (l : ℕ) (e : Edge l) : ℚ :=
  if l = 3 then U0 e
  else U Y (l-1) e - ∑ e' ∈ generators e, Y (l-1) e'

/-- Lemma 7: 1/v^s(Y^s) ∈ P_MI(k-1) -/
theorem lemma_7 (s : Commodity (k-1)) (h_vs_pos : v_s mcf s > 0) :
    Y s ∈ P_MI (k-1) := by

  -- Step 1: Non-negativity
  have h_nonneg : ∀ l e, 0 ≤ Y s l e := by
    intro l e
    unfold Y
    apply mul_nonneg
    · exact div_nonneg zero_le_one (le_of_lt h_vs_pos)
    · apply Finset.sum_nonneg
      intro a _
      exact mcf.f_s_nonneg s a

  -- Step 2: Sum constraints from MCF flow conservation
  have h_sum : ∀ l, 4 ≤ l ≤ k-1 →
      ∑ e ∈ net.edges_at_layer l, Y s l e = 1 := by
    intro l hl
    unfold Y
    have h_flow : ∑ e ∈ net.edges_at_layer l, Y_vector mcf s l e = v_s mcf s :=
      mcf.flow_through_layer l hl
    rw [← Finset.mul_sum, h_flow, mul_div_cancel' _ (ne_of_gt h_vs_pos)]

  -- Step 3: Base case - U^{(4)} ≥ 0
  have h_base : ∀ e : Edge 4, U (Y s) 3 e ≥ 0 := by
    intro e
    unfold U
    simp only [if_true]
    by_cases h : (e.i = 1 ∧ e.j = 2) ∨ (e.i = 1 ∧ e.j = 3) ∨ (e.i = 2 ∧ e.j = 3)
    · simp [U0, h]
      have : Y s 4 e ≤ 1 := by
        have : Y_vector mcf s 4 e ≤ v_s mcf s :=
          mcf.flow_through_node_le_total 4 e
        unfold Y
        rwa [div_le_iff h_vs_pos]
      linarith
    · simp [U0, h]
      exact h_nonneg 4 e

  -- Step 4: Prove all U^{(l)} ≥ 0 by induction
  have h_slacks : ∀ l e, 3 ≤ l → U (Y s) l e ≥ 0 := by
    intro l e hl
    induction' l using Nat.le_induction with l hl IH
    · exact h_base e
    · specialize IH (le_of_lt hl)

      by_contra h_neg
      have h_neg' : U (Y s) (l+1) e < 0 := h_neg

      have h_rec : U (Y s) (l+1) e = U (Y s) l e - ∑ e' ∈ generators e, Y s (l+1) e' := by
        unfold U
        simp [hl]

      rw [h_rec] at h_neg'
      have h_gt : ∑ e' ∈ generators e, Y s (l+1) e' > U (Y s) l e :=
        lt_sub_iff_add_lt.mp h_neg'

      let j := (generators e).head!.j

      have h_U_eq : U (Y s) l e =
          (∑ e' ∈ generators e, Y s j e') - ∑ m ∈ Ico (j+1) l, Y s m e := by
        induction' l using Nat.le_induction with l hl' IH_U
        · unfold U; simp [hl']; rfl
        · unfold U; simp [hl']; rw [IH_U (le_of_lt hl')]; ring

      have h_bound : Y s (l+1) e ≤
          (∑ e' ∈ generators e, Y s j e') - ∑ m ∈ Ico (j+1) l, Y s m e :=
        mcf.flow_bound_in_restricted_network s e j l

      rw [← h_U_eq] at h_bound

      have : Y s (l+1) e ≤ ∑ e' ∈ generators e, Y s (l+1) e' :=
        Finset.single_le_sum (fun _ _ => h_nonneg (l+1) _) (by simp)

      linarith [this, h_gt, h_bound]

  constructor
  · exact h_nonneg
  · exact h_sum
  · exact fun l e _ => h_slacks l e (by omega)
  · intro l hl
    have : U (Y s) (l-1) e - U (Y s) l e = ∑ e' ∈ generators e, Y s l e' := by
      unfold U; simp [hl]
    trivial

end MembershipProject.Core
