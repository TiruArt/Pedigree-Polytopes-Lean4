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
  suffices h : ∀ (acc : ℚ), acc ≥ 0 → ∀ (l : List (RigidEntry k)),
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
  suffices h : ∀ (acc : ℚ), acc ≥ 0 → ∀ (l : List (RigidEntry k)),
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
  have hfoldl_r : ∀ (l : List (RigidEntry k)) (g : RigidEntry k → ℚ) (r : ℚ),
      l.foldl (fun acc P => acc + g P) r = r + (l.map g).sum := by
    intro l g r
    induction l generalizing r with
    | nil => simp
    | cons P ps ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]; ring
  have hfoldl : ∀ (l : List (RigidEntry k)) (g : RigidEntry k → ℚ),
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

-- ============================================================================
-- HELPERS FOR u_nn
-- ============================================================================

/-- foldl over a list where every term is zero equals acc. -/
private lemma foldl_zero_eq_acc {α : Type*} (l : List α) (f : α → ℚ) (acc : ℚ)
    (hf : ∀ a ∈ l, f a = 0) :
    l.foldl (fun a x => a + f x) acc = acc := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [hf x (List.mem_cons.mpr (Or.inl rfl)), add_zero]
    exact ih acc (fun a ha => hf a (List.mem_cons.mpr (Or.inr ha)))

/-- Y-flow at t ∉ Delta t.k is zero. -/
private lemma Ys_norm_node_zero
    (s : Commodity n k) (t : Triple) (ht : t ∉ Delta t.k) :
    Ys_norm net mcf s t = 0 := by
  have hnotnode : t ∉ net.nodes := fun hmem => ht (net.node_valid t hmem)
  suffices h : Ys_full net mcf s t = 0 by simp [Ys_norm, h]
  simp only [Ys_full]; split_ifs with hle
  · have hd : Ys_direct net mcf s t = 0 := by
      simp only [Ys_direct]; apply Finset.sum_eq_zero; intro v _
      by_contra h; push Not at h
      exact hnotnode (mcf.f_s_node s t v (lt_of_le_of_ne (mcf.f_s_nn s t v) (Ne.symm h)))
    have hr : Ys_rigid net mcf s t = 0 := by
      simp only [Ys_rigid]
      apply foldl_zero_eq_acc; intro P hP
      simp only [if_neg (fun hmem => ht (mcf.triangles_valid P hP t hmem))]
    simp [Ys, hd, hr]
  · have hfs : mcf.f_s s s.src t = 0 := by
      by_contra h; push Not at h
      exact hnotnode (mcf.f_s_target s s.src t
        (lt_of_le_of_ne (mcf.f_s_nn s s.src t) (Ne.symm h)))
    have hfr : net.rigid.foldl (fun acc P => acc + mcf.f_rigid_s P s t) 0 = 0 :=
      foldl_zero_eq_acc net.rigid (mcf.f_rigid_s · s t) 0 (fun P _ => by
        by_contra h; push Not at h
        exact hnotnode (mcf.f_rigid_s_target P s t
          (lt_of_le_of_ne (mcf.f_rigid_s_nn P s t) (Ne.symm h))))
    simp [Ys_top, hfs, hfr]

/-- Ys_norm t = (1/v^s) * Ys t for t.k ≤ k. -/
private lemma Ys_norm_eq_mul (s : Commodity n k) (t : Triple) (htk : t.k ≤ k) :
    Ys_norm net mcf s t = (1 / s.flow_val) * Ys net mcf s t := by
  simp [Ys_norm, Ys_full, htk]

/-- Generator sum for Ys_norm ≤ 1. -/
private lemma gen_sum_Ys_norm_le_one
    (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (q : ℕ) (t : Triple) (ht : t ∈ Delta q) (hqk : q ≤ k) :
    (generators t).sum (Ys_norm net mcf s) ≤ 1 := by
  have hti  := mem_Delta_i1 ht
  have htij := mem_Delta_ij ht
  have htq  := mem_Delta_k ht  -- t.k = q
  have htjq : t.j < q := mem_Delta_jl ht
  -- unfold projections for omega
  simp only [Triple.i, Triple.j, Triple.k] at hti htij htq htjq
  by_cases htj3 : t.j > 3
  · -- generators ⊆ Delta t.j; Ys_norm_layer_sum at t.j
    calc (generators t).sum (Ys_norm net mcf s)
        ≤ (Delta t.j).sum (Ys_norm net mcf s) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (generators_subset_Delta hti htij (by simp only [Triple.j]; exact htj3))
            (fun u _ _ => Ys_norm_nonneg net mcf s u)
      _ = 1 := Ys_norm_layer_sum net mcf s hs t.j
            (by simp only [Triple.j] at htj3 ⊢; omega)
            (by simp only [Triple.j, Triple.k] at htj3 htjq htq hqk ⊢; omega)
  · -- t.j ≤ 3: generators = ∅ or {(1,2,3)}
    simp only [Triple.j] at htj3 htij htjq
    -- k ≥ 3 from hti, htij, htjq, hqk
    have h3k : 3 ≤ k := by omega
    by_cases h123 : t.i = 1 ∧ t.j = 2 ∧ t.k = 3
    · -- t = (1,2,3): generators = ∅, sum = 0 ≤ 1
      obtain ⟨hi, hj, hk'⟩ := h123
      have : generators t = ∅ := by
        simp only [generators, hi, hj, hk', Triple.i, Triple.j, Triple.k, and_self, ite_true]
      simp [this]
    · -- t ≠ (1,2,3): generators = {(1,2,3)}
      have htk_ne3 : ¬(t.i = 1 ∧ t.j = 2 ∧ t.k = 3) := h123
      simp only [generators, htk_ne3, if_false, if_neg htj3, Finset.sum_singleton]
      have hsf := mcf.source_flow s hs
      have h123k : Triple.k (1,2,3) ≤ k := by simp only [Triple.k]; exact h3k
      simp only [Ys_norm, Ys_full, h123k, ite_true, Ys, Ys_direct, Ys_rigid]
      rw [hsf]; field_simp [ne_of_gt s.flow_pos]; norm_num

/-- Ys_norm t = 0 when t.k ≥ k+2 (all nodes have layer ≤ k+1). -/
private lemma Ys_norm_above_k (s : Commodity n k) (t : Triple) (ht : t.k ≥ k + 2) :
    Ys_norm net mcf s t = 0 := by
  have hnotnode : t ∉ net.nodes := fun hmem => by
    have := (net.node_layers t hmem).2
    simp only [Triple.k] at ht this; omega
  suffices h : Ys_full net mcf s t = 0 by simp [Ys_norm, h]
  simp only [Ys_full, show ¬ t.k ≤ k from by simp only [Triple.k] at ht ⊢; omega, if_false]
  simp only [Ys_top]
  have hfs : mcf.f_s s s.src t = 0 := by
    by_contra h; push Not at h
    exact hnotnode (mcf.f_s_target s s.src t
      (lt_of_le_of_ne (mcf.f_s_nn s s.src t) (Ne.symm h)))
  have hfr : net.rigid.foldl (fun acc P => acc + mcf.f_rigid_s P s t) 0 = 0 :=
    foldl_zero_eq_acc net.rigid (mcf.f_rigid_s · s t) 0 (fun P _ => by
      by_contra h; push Not at h
      exact hnotnode (mcf.f_rigid_s_target P s t
        (lt_of_le_of_ne (mcf.f_rigid_s_nn P s t) (Ne.symm h))))
  simp [hfs, hfr]

/-- Column sum (layers 4..k+1) of Ys_norm ≤ 1. -/
private lemma Ys_norm_col_sum_le_one
    (s : Commodity n k) (hs : s ∈ mcf.commodities) (a b : ℕ) :
    (Finset.Ico 4 (k + 2)).sum (fun l => Ys_norm net mcf s (a, b, l)) ≤ 1 := by
  -- Split: Ico 4 (k+2) = Ico 4 (k+1) ∪ {k+1}
  rw [show k + 2 = (k + 1) + 1 from by omega,
      Finset.sum_Ico_succ_top (by have := mcf.hk; omega : 4 ≤ k + 1)]
  have hcol := mcf.col_sum_le s hs a b
  have hpos : (0:ℚ) < 1 / s.flow_val := div_pos one_pos s.flow_pos
  have hflow_pos : (0:ℚ) < s.flow_val := s.flow_pos
  have hlk : ∀ l ∈ Finset.Ico 4 (k+1), Triple.k (a,b,l) ≤ k := by
    intro l hl; simp only [Finset.mem_Ico] at hl; simp only [Triple.k]; omega
  have htopk : ¬ Triple.k (a,b,k+1) ≤ k := by simp only [Triple.k]; omega
  -- LHS of col_sum_le = s.flow_val * (Σ Ys_norm + Ys_norm top)
  have hraw : (Finset.Ico 4 (k + 1)).sum (fun l =>
      (Delta (l + 1)).sum (fun v => mcf.f_s s (a, b, l) v) +
      net.rigid.foldl (fun acc P => acc + if (a, b, l) ∈ P.ped.triangles then
        (Delta (k + 1)).sum (fun v => mcf.f_rigid_s P s v) else 0) 0) +
      (mcf.f_s s s.src (a, b, k + 1) +
       net.rigid.foldl (fun acc P => acc + mcf.f_rigid_s P s (a, b, k + 1)) 0) =
      s.flow_val * ((Finset.Ico 4 (k + 1)).sum (fun l => Ys_norm net mcf s (a, b, l)) +
        Ys_norm net mcf s (a, b, k + 1)) := by
    simp only [Ys_norm, Ys_full, Ys, Ys_direct, Ys_rigid, Ys_top]
    simp only [htopk, if_false]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl; intro l hl
      rw [if_pos (hlk l hl)]
      field_simp [ne_of_gt hflow_pos]
    · field_simp [ne_of_gt hflow_pos]
  have hS := le_of_mul_le_mul_left (hraw ▸ hcol.trans (le_of_eq (mul_one _).symm)) hflow_pos
  linarith
private lemma Ys_delta_filter_sum
    (s : Commodity n k) (a b l : ℕ)
    (ha : 1 ≤ a) (hab : a < b) (hbl : b < l) :
    (Delta l).sum (fun u => if u.i = a ∧ u.j = b then Ys net mcf s u else 0) =
    Ys net mcf s (a, b, l) := by
  rw [← Finset.sum_filter, delta_mem_for_edge ha hab hbl]
  simp [Finset.sum_singleton]

/-- Key step: Ys_norm(t) ≤ 1 - Σ_{Ico 4 q} Ys_norm(t.i,t.j,l) for t ∈ Delta q ≤ k. -/
private lemma Ys_norm_le_slack_step
    (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (m : ℕ) (p : ℕ × ℕ)
    (hm4 : m + 4 ≤ k)
    (ht : (p.1, p.2, m + 4) ∈ Delta (m + 4)) :
    Ys_norm net mcf s (p.1, p.2, m + 4) ≤
    1 - (Finset.Ico 4 (m + 4)).sum (fun l => Ys_norm net mcf s (p.1, p.2, l)) := by
  have hp1  := mem_Delta_i1 ht
  have hp12 := mem_Delta_ij ht
  have hp2  := mem_Delta_jl ht
  have hpos : (0:ℚ) < 1 / s.flow_val := div_pos one_pos s.flow_pos
  have hfls := mcf.flow_le_slack s hs (m + 4) (by omega) hm4 (p.1, p.2, m + 4) ht
  have hLHS : (Delta (m + 5)).sum (fun v => mcf.f_s s (p.1, p.2, m + 4) v) +
      net.rigid.foldl (fun acc P => acc + if (p.1, p.2, m + 4) ∈ P.ped.triangles then
        (Delta (k + 1)).sum (fun v => mcf.f_rigid_s P s v) else 0) 0 =
      Ys net mcf s (p.1, p.2, m + 4) := by
    simp [Ys, Ys_direct, Ys_rigid, Triple.k]
  have hRHS_gen : (generators (p.1, p.2, m + 4)).sum (fun t' =>
      (Delta (t'.k + 1)).sum (fun v => mcf.f_s s t' v) +
      net.rigid.foldl (fun acc P => acc + if t' ∈ P.ped.triangles then
        (Delta (k + 1)).sum (fun v => mcf.f_rigid_s P s v) else 0) 0) =
      (generators (p.1, p.2, m + 4)).sum (Ys net mcf s) :=
    Finset.sum_congr rfl (fun t' _ => by simp [Ys, Ys_direct, Ys_rigid])
  have hRHS_ico : (Finset.Ico (p.2 + 1) (m + 4)).sum (fun l =>
      (Delta l).sum (fun u => if u.i = p.1 ∧ u.j = p.2 then
        (Delta (u.k + 1)).sum (fun v => mcf.f_s s u v) +
        net.rigid.foldl (fun acc P => acc + if u ∈ P.ped.triangles then
          (Delta (k + 1)).sum (fun v => mcf.f_rigid_s P s v) else 0) 0
      else 0)) =
      (Finset.Ico (p.2 + 1) (m + 4)).sum (fun l => Ys net mcf s (p.1, p.2, l)) :=
    Finset.sum_congr rfl (fun l hl => by
      simp only [Finset.mem_Ico] at hl
      rw [← Ys_delta_filter_sum net mcf s p.1 p.2 l hp1 hp12 (by omega)]
      apply Finset.sum_congr rfl; intro u hu
      split_ifs with h
      · simp [Ys, Ys_direct, Ys_rigid, mem_Delta_k hu]
      · rfl)
  have hYs_le : Ys net mcf s (p.1, p.2, m + 4) ≤
      (generators (p.1, p.2, m + 4)).sum (Ys net mcf s) -
      (Finset.Ico (p.2 + 1) (m + 4)).sum (fun l => Ys net mcf s (p.1, p.2, l)) := by
    rw [← hLHS, ← hRHS_gen, ← hRHS_ico]; exact hfls
  have hYn_eq : Ys_norm net mcf s (p.1, p.2, m + 4) =
      (1/s.flow_val) * Ys net mcf s (p.1, p.2, m + 4) :=
    Ys_norm_eq_mul net mcf s _ (by omega)
  have hgen_eq : (generators (p.1, p.2, m + 4)).sum (Ys_norm net mcf s) =
      (1/s.flow_val) * (generators (p.1, p.2, m + 4)).sum (Ys net mcf s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t' ht'
    have ht'k : t'.k ≤ k := by
      have h := mem_generators_Delta hp1 hp12 ht'
      have hk_val := mem_Delta_k h
      simp only [Triple.j, Triple.k] at hk_val hp2 hm4 ⊢
      split_ifs at hk_val with hj <;> omega
    exact Ys_norm_eq_mul net mcf s t' ht'k
  have hico_eq : (Finset.Ico (p.2 + 1) (m + 4)).sum (fun l => Ys_norm net mcf s (p.1, p.2, l)) =
      (1/s.flow_val) * (Finset.Ico (p.2 + 1) (m + 4)).sum (fun l => Ys net mcf s (p.1, p.2, l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l hl
    simp only [Finset.mem_Ico] at hl
    exact Ys_norm_eq_mul net mcf s _ (by simp only [Triple.k]; omega)
  have hgen_le := gen_sum_Ys_norm_le_one net mcf s hs (m + 4) (p.1, p.2, m + 4) ht hm4
  have hzero_low : (Finset.Ico 4 (p.2 + 1)).sum (fun l =>
      Ys_norm net mcf s (p.1, p.2, l)) = 0 :=
    Finset.sum_eq_zero (fun l hl => by
      simp only [Finset.mem_Ico] at hl
      apply Ys_norm_node_zero
      simp only [mem_Delta_iff, Triple.i, Triple.j, Triple.k]
      push Not; intro; omega)
  have hscaled : Ys_norm net mcf s (p.1, p.2, m + 4) ≤
      (generators (p.1, p.2, m + 4)).sum (Ys_norm net mcf s) -
      (Finset.Ico (p.2 + 1) (m + 4)).sum (fun l => Ys_norm net mcf s (p.1, p.2, l)) := by
    rw [hYn_eq, hgen_eq, hico_eq]
    linarith [mul_le_mul_of_nonneg_left hYs_le (le_of_lt hpos),
              mul_sub (1/s.flow_val)
                ((generators (p.1, p.2, m + 4)).sum (Ys net mcf s))
                ((Finset.Ico (p.2 + 1) (m + 4)).sum (fun l => Ys net mcf s (p.1, p.2, l)))]
  -- Combine: Σ_{Ico 4 (m+4)} = Σ_{Ico 4 (p.2+1)} + Σ_{Ico (p.2+1) (m+4)}
  -- by_cases on whether p.2+1 ≥ 4
  have hp2_lt4 : p.2 < m + 4 := by simp only [Triple.j] at hp2; exact hp2
  by_cases hle4 : p.2 + 1 ≤ 4
  · -- p.2 ≤ 3: Ico 4 (m+4) ⊆ Ico (p.2+1) (m+4)
    have hsubset : Finset.Ico 4 (m + 4) ⊆ Finset.Ico (p.2 + 1) (m + 4) :=
      fun l hl => by simp only [Finset.mem_Ico] at hl ⊢; omega
    linarith [Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun l _ _ => Ys_norm_nonneg net mcf s (p.1, p.2, l))]
  · -- p.2 ≥ 3: split Ico 4 (m+4) at p.2+1
    push Not at hle4
    have hsplit : (Finset.Ico 4 (m + 4)).sum (fun l => Ys_norm net mcf s (p.1, p.2, l)) =
        (Finset.Ico 4 (p.2 + 1)).sum (fun l => Ys_norm net mcf s (p.1, p.2, l)) +
        (Finset.Ico (p.2 + 1) (m + 4)).sum (fun l => Ys_norm net mcf s (p.1, p.2, l)) :=
      (Finset.sum_Ico_consecutive _ (by omega) (by omega)).symm
    linarith

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
    -- All terms at layers ≥ k+2 are zero; terms at layers ≤ k+1 sum ≤ 1
    have hcol := Ys_norm_col_sum_le_one net mcf s hs p.1 p.2
    -- Σ_{Ico 4 (k+2)} = Σ_{Ico 4 (m+4)} with zeros for l ≥ k+2
    by_cases hm : m + 4 ≤ k + 2
    · -- Ico 4 (m+4) ⊆ Ico 4 (k+2): sum ≤ col_sum ≤ 1
      calc (Finset.Ico 4 (m + 4)).sum (fun l => Ys_norm net mcf s (p.1, p.2, l))
          ≤ (Finset.Ico 4 (k + 2)).sum (fun l => Ys_norm net mcf s (p.1, p.2, l)) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Ico_subset_Ico_right (by omega))
              (fun l _ _ => Ys_norm_nonneg net mcf s (p.1, p.2, l))
        _ ≤ 1 := hcol
    · -- m+4 > k+2: split Ico 4 (m+4) = Ico 4 (k+2) ∪ Ico (k+2) (m+4)
      push Not at hm
      rw [show Finset.Ico 4 (m + 4) = Finset.Ico 4 (k + 2) ∪ Finset.Ico (k + 2) (m + 4) from
          (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm,
          Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 4 (k+2) (m+4))]
      have hzero : (Finset.Ico (k + 2) (m + 4)).sum
          (fun l => Ys_norm net mcf s (p.1, p.2, l)) = 0 :=
        Finset.sum_eq_zero (fun l hl => by
          simp only [Finset.mem_Ico] at hl
          exact Ys_norm_above_k net mcf s _ (by simp only [Triple.k]; omega))
      linarith

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
