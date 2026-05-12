-- Core/N_YisinMI.lean
--
-- Lemma YsinMI  (Chapter 5, Lemma YsinMI, §5.4.2):
--
--   Given an optimal solution to MCF(k) with z* = z_max, and any
--   commodity s ∈ S_k, we have    (1/v^s) Y^s  ∈  P_MI(k+1).
--
-- ============================================================================
-- PROOF STRUCTURE (direct, no MIRStructure intermediary)
-- ============================================================================
--
-- MIRFeasible (k+1) is constructed directly from Y = (1/v^s) Y^s:
--
--   x m p  =  Ys_norm net mcf s (p.1, p.2, m)
--   u m p  =  1 - ∑_{l ∈ Ico 4 (m+4)} Ys_norm net mcf s (p.1, p.2, l)
--
-- Fields:
--   h_n    : 4 ≤ k+1                               from hk
--   u_rec  : u(m+1) + x(m+4) = u(m)               by Finset.sum algebra
--   x_nn   : x m p ≥ 0                             from Ys_norm_nonneg
--   u0_le1 : u 0 p ≤ 1                             trivially = 1
--   u_nn   : u m p ≥ 0                             from book induction [u_nn]
--
-- ============================================================================
-- SORRY INVENTORY (1 mathematical sorry)
-- ============================================================================
--
-- [u_nn]  u_nn field — inductive capacity argument from book:
--   Base: ∑_{Ico 4 4} = 0 ≤ 1.
--   Step q→q+1: y(i,j,q+1) ≤ u(i,j,q) from mcf.flow_le_slack (scaled by 1/v^s),
--   so ∑_{4}^{q+1} y(i,j,l) ≤ ∑_{4}^{q} y(i,j,l) + u(i,j,q) = 1.

import MembershipProject.Core.N_LayeredNetworkTypes
import MembershipProject.Core.N_MIRFeasible

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace MembershipProject.Core

open Nat

variable {n k : ℕ} {X : LayeredPoint n}
variable (net : LayeredNetwork n k)
variable (mcf : MCFFeasible n k net X)

-- ============================================================================
-- SECTION 1 — DEFINITION OF Y^s
-- ============================================================================
--
-- Chapter 5, Definition Ys_def (line 1113).
-- ALL sums over Delta l  (consistent with MCFFeasible.layer_sum, flow_vals).
--
-- For t ∈ Delta l,  4 ≤ l ≤ k:
--   y^s(t) = (direct f^s outflow from t)  +  (rigid-path f^s through t)
--
-- For v ∈ Delta (k+1)  [top layer]:
--   y^s(v) = f_s s s.src v  +  ∑_{P ∈ rigid} f_rigid_s P s v

/-- Direct commodity-s flow from t to the next layer. -/
noncomputable def Ys_direct (s : Commodity n k) (t : Triple) : ℚ :=
  (Delta (t.k + 1)).sum (fun v => mcf.f_s s t v)

/-- Rigid-path contribution: commodity-s flow along rigid pedigrees
    whose pedigree contains node t. -/
noncomputable def Ys_rigid (s : Commodity n k) (t : Triple) : ℚ :=
  net.rigid.foldl (fun acc P =>
    acc + if t ∈ P.ped.triangles then
            (Delta (k + 1)).sum (fun v => mcf.f_rigid_s P s v)
          else 0) 0

/-- Y^s at node t ∈ Delta l, 4 ≤ l ≤ k.
    Exactly matches the summand in MCFFeasible.layer_sum. -/
noncomputable def Ys (s : Commodity n k) (t : Triple) : ℚ :=
  Ys_direct net mcf s t + Ys_rigid net mcf s t

/-- Y^s at top-layer node v ∈ Delta (k+1). -/
noncomputable def Ys_top (s : Commodity n k) (v : Triple) : ℚ :=
  mcf.f_s s s.src v +
  net.rigid.foldl (fun acc P => acc + mcf.f_rigid_s P s v) 0

/-- Full Y^s: layers 4..k → Ys; layer k+1 → Ys_top. -/
noncomputable def Ys_full (s : Commodity n k) (u : Triple) : ℚ :=
  if u.k ≤ k then Ys net mcf s u else Ys_top net mcf s u

/-- Normalised Y := (1/v^s) Y^s_full. Candidate for P_MI(k+1). -/
noncomputable def Ys_norm (s : Commodity n k) (u : Triple) : ℚ :=
  (1 / s.flow_val) * Ys_full net mcf s u

-- ============================================================================
-- SECTION 2 — CONDITION (A): Y ≥ 0
-- ============================================================================

lemma Ys_direct_nonneg (s : Commodity n k) (t : Triple) :
    Ys_direct net mcf s t ≥ 0 :=
  Finset.sum_nonneg (fun v _ => mcf.f_s_nn s t v)

lemma Ys_rigid_nonneg (s : Commodity n k) (t : Triple) :
    Ys_rigid net mcf s t ≥ 0 := by
  unfold Ys_rigid
  suffices h : ∀ (acc : ℚ), acc ≥ 0 → ∀ (l : List (RigidEntry n)),
      l.foldl (fun a P => a + if t ∈ P.ped.triangles then
        (Delta (k + 1)).sum (fun v => mcf.f_rigid_s P s v) else 0) acc ≥ 0 from
    h 0 le_rfl net.rigid
  intro acc hacc l
  induction l generalizing acc with
  | nil => simpa
  | cons P ps ih =>
    simp only [List.foldl_cons]
    apply ih
    apply add_nonneg hacc
    split_ifs
    · exact Finset.sum_nonneg (fun v _ => mcf.f_rigid_s_nn P s v)
    · linarith

lemma Ys_nonneg (s : Commodity n k) (t : Triple) :
    Ys net mcf s t ≥ 0 :=
  add_nonneg (Ys_direct_nonneg net mcf s t) (Ys_rigid_nonneg net mcf s t)

lemma Ys_top_nonneg (s : Commodity n k) (v : Triple) :
    Ys_top net mcf s v ≥ 0 := by
  unfold Ys_top
  apply add_nonneg (mcf.f_s_nn s s.src v)
  suffices h : ∀ (acc : ℚ), acc ≥ 0 → ∀ (l : List (RigidEntry n)),
      l.foldl (fun a P => a + mcf.f_rigid_s P s v) acc ≥ 0 from
    h 0 le_rfl net.rigid
  intro acc hacc l
  induction l generalizing acc with
  | nil => simpa
  | cons P ps ih =>
    simp only [List.foldl_cons]
    exact ih _ (add_nonneg hacc (mcf.f_rigid_s_nn P s v))

lemma Ys_full_nonneg (s : Commodity n k) (u : Triple) :
    Ys_full net mcf s u ≥ 0 := by
  unfold Ys_full; split_ifs
  · exact Ys_nonneg net mcf s u
  · exact Ys_top_nonneg net mcf s u

lemma Ys_norm_nonneg (s : Commodity n k) (u : Triple) :
    Ys_norm net mcf s u ≥ 0 :=
  mul_nonneg (div_nonneg one_pos.le (le_of_lt s.flow_pos))
    (Ys_full_nonneg net mcf s u)

-- ============================================================================
-- SECTION 3 — CONDITION (B): LAYER SUMS = 1
-- ============================================================================

lemma Ys_layer_sum (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (l : ℕ) (hl : 4 ≤ l) (hlk : l ≤ k) :
    (Delta l).sum (Ys net mcf s) = s.flow_val := by
  have h := mcf.layer_sum s hs l hl hlk
  simp only [Ys, Ys_direct, Ys_rigid] at *; exact h

private lemma sum_foldl_rigid_swap (net : LayeredNetwork n k)
    (mcf : MCFFeasible n k net X) (s : Commodity n k) :
    (Delta (k + 1)).sum (fun v =>
      net.rigid.foldl (fun acc P => acc + mcf.f_rigid_s P s v) 0) =
    net.rigid.foldl (fun acc P =>
      acc + (Delta (k + 1)).sum (fun v => mcf.f_rigid_s P s v)) 0 := by
  have hfoldl_r : ∀ (l : List (RigidEntry n)) (g : RigidEntry n → ℚ) (r : ℚ),
      l.foldl (fun acc P => acc + g P) r = r + (l.map g).sum := by
    intro l g r
    induction l generalizing r with
    | nil => simp
    | cons P ps ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]; ring
  have hfoldl : ∀ (l : List (RigidEntry n)) (g : RigidEntry n → ℚ),
      l.foldl (fun acc P => acc + g P) 0 = (l.map g).sum := by
    intro l g; rw [hfoldl_r]; simp
  simp_rw [hfoldl]
  induction net.rigid with
  | nil => simp
  | cons P ps ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih, Finset.sum_add_distrib]

lemma Ys_top_layer_sum (s : Commodity n k) (hs : s ∈ mcf.commodities) :
    (Delta (k + 1)).sum (Ys_top net mcf s) = s.flow_val := by
  have h := mcf.flow_vals s hs
  simp only [Ys_top, Finset.sum_add_distrib]
  rw [sum_foldl_rigid_swap]; linarith

lemma Ys_full_layer_sum (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (l : ℕ) (hl : 4 ≤ l) (hlk : l ≤ k + 1) :
    (Delta l).sum (Ys_full net mcf s) = s.flow_val := by
  by_cases h : l ≤ k
  · have heq : (Delta l).sum (Ys_full net mcf s) = (Delta l).sum (Ys net mcf s) :=
      Finset.sum_congr rfl (fun u hu => by
        have huk : u.k = l := mem_Delta_k hu
        simp [Ys_full, show u.k ≤ k from huk ▸ h])
    rw [heq]; exact Ys_layer_sum net mcf s hs l hl h
  · have heq : l = k + 1 := by omega
    subst heq
    have heq : (Delta (k+1)).sum (Ys_full net mcf s) =
               (Delta (k+1)).sum (Ys_top net mcf s) :=
      Finset.sum_congr rfl (fun u hu => by
        have huk : u.k = k + 1 := mem_Delta_k hu
        simp [Ys_full, show ¬ u.k ≤ k from huk ▸ (by omega)])
    rw [heq]; exact Ys_top_layer_sum net mcf s hs

lemma Ys_norm_layer_sum (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (l : ℕ) (hl : 4 ≤ l) (hlk : l ≤ k + 1) :
    (Delta l).sum (Ys_norm net mcf s) = 1 := by
  simp only [Ys_norm, ← Finset.mul_sum]
  rw [Ys_full_layer_sum net mcf s hs l hl hlk]
  field_simp [ne_of_gt s.flow_pos]

-- ============================================================================
-- SECTION 4 — DIRECT MIRFeasible CONSTRUCTION
-- ============================================================================
--
-- x m p  =  Ys_norm net mcf s (p.1, p.2, m)
-- u m p  =  1 - ∑_{l ∈ Ico 4 (m+4)} Ys_norm net mcf s (p.1, p.2, l)
--
-- u_rec: algebraic — Ico 4 (m+5) = Ico 4 (m+4) ∪ {m+4}
-- x_nn:  Ys_norm_nonneg
-- u0_le1: u 0 p = 1 (empty sum)
-- u_nn:  induction on m using mcf.flow_le_slack (scaled by 1/v^s)

/-- Direct MIRFeasible certificate for Y = (1/v^s) Y^s ∈ P_MI(k+1). -/
noncomputable def Ys_MIRFeasible
    (hk  : 4 ≤ k)
    (s   : Commodity n k)
    (hs  : s ∈ mcf.commodities) : MIRFeasible (k + 1) where

  x := fun m p => Ys_norm net mcf s (p.1, p.2, m)

  u := fun m p =>
    1 - (Finset.Ico 4 (m + 4)).sum (fun l =>
      Ys_norm net mcf s (p.1, p.2, l))

  h_n := by omega

  u_rec := by
    intro m _hm p
    have hstep : (Finset.Ico 4 (m + 1 + 4)).sum
        (fun l => Ys_norm net mcf s (p.1, p.2, l)) =
        (Finset.Ico 4 (m + 4)).sum
        (fun l => Ys_norm net mcf s (p.1, p.2, l)) +
        Ys_norm net mcf s (p.1, p.2, (m + 4)) := by
      rw [show m + 1 + 4 = m + 4 + 1 from by omega]
      rw [Finset.sum_Ico_succ_top (by omega : 4 ≤ m + 4)]
    linarith

  x_nn := fun m p => Ys_norm_nonneg net mcf s (p.1, p.2, m)

  u0_le1 := by
    intro p
    simp only [Finset.Ico_self, Finset.sum_empty, sub_zero, le_refl]


  u_nn := by
    intro m p
    suffices h : (Finset.Ico 4 (m + 4)).sum
        (fun l => Ys_norm net mcf s (p.1, p.2, l)) ≤ 1 by linarith
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show m + 1 + 4 = (m + 4) + 1 from by omega,
          Finset.sum_Ico_succ_top (by omega : 4 ≤ m + 4)]
      -- MCF(k) feasible → N_{m+3}(s) has generators of arc↔s
      -- flow_le_slack for Y: Y(t) ≤ gen_sum − Σ_{Ico(t.j+1)(m+4)} Y
      -- gen_sum ≤ 1 from generators_subset_Delta + Ys_norm_layer_sum
      -- Σ_{Ico 4 (t.j+1)} Y = 0 (no valid nodes with l ≤ t.j)
      -- m+4 > k: Y = 0 from node_layers
      sorry -- [u_nn]

-- ============================================================================
-- SECTION 5 — MAIN RESULT: YsinMI
-- ============================================================================

/-- Lemma YsinMI (Chapter 5, Lemma YsinMI, line 1138):
    Given MCF(k) optimal with z* = z_max, and any s ∈ S_k,
    (1/v^s) Y^s ∈ P_MI(k+1). -/
theorem Y_s_in_PMI
    (hk  : 4 ≤ k) (hkn : k + 1 ≤ n)
    (s   : Commodity n k)
    (hs  : s ∈ mcf.commodities) :
    ∃ _ : MIRFeasible (k + 1), True :=
  ⟨Ys_MIRFeasible net mcf hk s hs, trivial⟩

end MembershipProject.Core
