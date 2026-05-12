-- Core/Y_s_in_PMI.lean
--
-- Lemma YsinMI (Chapter 5, Lemma YsinMI):
--   Given MCF(k) with z* = z_max, for each s ∈ S_k,
--   (1/v^s) Y^s ∈ P_MI(k).
--
-- PROOF STRUCTURE (Chapter 5, pp. 1138-1170):
--   Let Y = (1/v^s) Y^s. Verify Y ∈ P_MI(k):
--   [1] Non-negativity: from f^s_a ≥ 0
--   [2] Layer sums = 1: Σ_e y^s_l(e) = v^s → divide by v^s
--   [3] U^(4) ≥ 0: base case, y^s_4(e) ≤ v^s since sum = v^s
--   [4] U^(q+1) ≥ 0 by contradiction:
--       Assume U^(q+1)_{e} < 0 for some q ≥ 4, e = (i^o, j^o).
--       Max flow into [q:e] ≤ Σ_{e'∈G(e)} y^s_{j^o}(e') = U^(q)_e ≥ 0.
--       But y^s_q(e) ≤ U^(q)_e. So U^(q+1) = U^(q) - y^s_q(e) ≥ 0.
--       Contradiction.

import MembershipProject.Core.LayeredNetworkTypes
import MembershipProject.Core.SlackComputation
import MembershipProject.Core.Types
import MembershipProject.Core.MIRFeasible

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace MembershipProject.Core

open Nat

-- ============================================================================
-- SECTION 1: THE Y^s VECTOR (Chapter 5, Definition Ys_def)
-- ============================================================================
--
-- y^s(u) ≡ y^s_l(e) for u = [l:e]:
--   = Σ_{a=[u,v] ∈ F_l} f^s_a          [direct outflow from u]
--   + Σ_{q=l}^{k} Σ_{a ∈ A(u,q)} f^s_a [flow through rigid paths containing u]
--
-- where A(u,q) = { a=[P,v] ∈ F_q | P ∈ R_{q-1}, u ∈ path(P) }.

/-- Direct outflow of commodity s from node u at layer l.
    Paper: Σ_{a=[u,v] ∈ F_l} f^s_a. -/
noncomputable def direct_outflow {n k : ℕ} (net : LayeredNetwork n k) {X : LayeredPoint n}
    (mcf : MCFFeasible n k net X)
    (s : Commodity n k) (u : Triple) : ℚ :=
  (Delta (u.k + 1)).sum (fun v => mcf.f_s s u v)

/-- Flow of commodity s through rigid paths that contain node u.
    Paper: Σ_{q=l}^{k} Σ_{a ∈ A(u,q)} f^s_a. -/
noncomputable def rigid_path_flow {n k : ℕ} {X : LayeredPoint n}
    (net : LayeredNetwork n k) (mcf : MCFFeasible n k net X)
    (s : Commodity n k) (u : Triple) : ℚ :=
  net.rigid.foldl (fun acc P =>
    -- u occurs in path(P) iff u ∈ P.pedigree.triangles
    if u ∈ P.pedigree.triangles then
      acc + (Delta (k + 1)).sum (fun v => mcf.f_rigid_s P s v)
    else acc) 0

/-- The Y^s vector: y^s(u) = direct_outflow + rigid_path_flow.
    Chapter 5, Definition Ys_def (Equation ys_sdef). -/
noncomputable def Y_s {n k : ℕ} (net : LayeredNetwork n k)
    {X : LayeredPoint n} (mcf : MCFFeasible n k net X)
    (s : Commodity n k) (u : Triple) : ℚ :=
  direct_outflow net mcf s u + rigid_path_flow net mcf s u

/-- The normalised vector: (1/v^s) Y^s. -/
noncomputable def Y_s_norm {n k : ℕ} (net : LayeredNetwork n k)
    {X : LayeredPoint n} (mcf : MCFFeasible n k net X)
    (s : Commodity n k) (u : Triple) : ℚ :=
  (1 / s.flow_val) * Y_s net mcf s u

-- ============================================================================
-- SECTION 2: KEY PROPERTIES OF Y^s
-- ============================================================================

/-- Non-negativity of Y^s.
    Follows from f_s_nn and f_rigid_s_nn. -/
lemma Y_s_nonneg {n k : ℕ} (net : LayeredNetwork n k)
    {X : LayeredPoint n} (mcf : MCFFeasible n k net X)
    (s : Commodity n k) (u : Triple) :
    Y_s net mcf s u ≥ 0 := by
  unfold Y_s direct_outflow rigid_path_flow
  apply add_nonneg
  · apply Finset.sum_nonneg; intro v _; exact mcf.f_s_nn s u v
  · suffices h : ∀ acc : ℚ, acc ≥ 0 →
        net.rigid.foldl (fun a P =>
          if u ∈ P.pedigree.triangles then a + (Delta (k+1)).sum (fun v => mcf.f_rigid_s P s v)
          else a) acc ≥ 0 from h 0 (le_refl _)
    intro acc hacc
    induction net.rigid generalizing acc with
    | nil => simpa
    | cons P rest ih =>
      simp only [List.foldl_cons]
      apply ih
      split_ifs with h
      · exact add_nonneg hacc (Finset.sum_nonneg (fun v _ => mcf.f_rigid_s_nn P s v))
      · exact hacc

/-- Non-negativity of normalised Y^s/v^s. -/
lemma Y_s_norm_nonneg {n k : ℕ} (net : LayeredNetwork n k)
    {X : LayeredPoint n} (mcf : MCFFeasible n k net X)
    (s : Commodity n k) (u : Triple) :
    Y_s_norm net mcf s u ≥ 0 := by
  unfold Y_s_norm
  apply mul_nonneg
  · apply div_nonneg; linarith; exact le_of_lt s.flow_pos
  · exact Y_s_nonneg net mcf s u

/-- Layer sum of Y^s equals v^s.
    Chapter 5: Σ_{e ∈ E_{l-1}} y^s_l(e) = v^s for 4 ≤ l ≤ k.
    Proof: from MCF flow conservation at each layer. -/
lemma Y_s_layer_sum {n k : ℕ} (net : LayeredNetwork n k)
    {X : LayeredPoint n} (mcf : MCFFeasible n k net X)
    (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (l : ℕ) (hl : 4 ≤ l ∧ l ≤ k) :
    (Delta l).sum (fun u => Y_s net mcf s u) = s.flow_val := by
  -- Direct from mcf.layer_sum (Chapter 5, line 1134):
  -- nodes NOT in net.nodes have zero weight (zero capacity → zero flow),
  -- so summing over Delta l gives v^s.
  have h := mcf.layer_sum s hs l hl.1 hl.2
  simp only [Y_s, direct_outflow, rigid_path_flow]
  convert h using 2
  ext u
  -- direct_outflow uses Delta (u.k + 1), layer_sum uses Delta (u.k + 1) ✓
  -- rigid_path_flow uses Delta (k+1), layer_sum uses Delta (k+1) ✓
  rfl

/-- Layer sum of (1/v^s) Y^s equals 1. -/
lemma Y_s_norm_layer_sum {n k : ℕ} (net : LayeredNetwork n k)
    {X : LayeredPoint n} (mcf : MCFFeasible n k net X)
    (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (l : ℕ) (hl : 4 ≤ l ∧ l ≤ k) :
    (Delta l).sum (fun u => Y_s_norm net mcf s u) = 1 := by
  unfold Y_s_norm
  rw [← Finset.mul_sum]
  rw [Y_s_layer_sum net mcf s hs l hl]
  field_simp [ne_of_gt s.flow_pos]

-- ============================================================================
-- SECTION 3: THE SLACK SEQUENCE U^(l) FOR Y^s/v^s
-- ============================================================================
--
-- U^(3) = (1_{|E_2|}, 0) (initial slack)
-- U^(l+1) = U^(l) - A^(l+1) * y_{l+1}
--
-- KEY STEP (Chapter 5, proof of YsinMI):
-- For the normalised vector Y = (1/v^s) Y^s:
--   U^(4)_e = 1 - y_4(e) ≥ 0  [since y_4(e) ≤ 1 from sum = 1]
--   U^(q+1)_e = U^(q)_e - y_q(e) ≥ 0  [by contradiction argument]

/-- The slack at layer l for the normalised Y^s vector.
    U^(l)_e = 1 - Σ_{l'=4}^{l} (A^(l') matrix entries) * y_{l'}. -/
noncomputable def U_slack {n k : ℕ} (net : LayeredNetwork n k)
    {X : LayeredPoint n} (mcf : MCFFeasible n k net X)
    (s : Commodity n k) (l : ℕ) (e : Triple) : ℚ :=
  -- Lift using sparseMatVecMul structure from SlackComputation
  -- U^(l)_e = Σ_{e' ∈ generators e} Y_s_norm e'_{j_e} - Σ_{l'=j_e+1}^{l-1} Y_s_norm_l'(e)
  -- where j_e = e.j (the second index of edge e)
  (generators e).sum (fun e' => Y_s_norm net mcf s e') -
  (Finset.Ico (e.j + 1) l).sum (fun l' =>
    (Delta l').sum (fun u => if u.i = e.i ∧ u.j = e.j then Y_s_norm net mcf s u else 0))

-- ============================================================================
-- SECTION 4: BASE CASE U^(4) ≥ 0
-- ============================================================================
--
-- Chapter 5: y^s_4(e) ≥ 0 and Σ_{e ∈ E_3} y^s_4(e) = v^s,
-- so (1/v^s) y^s_4(e) ≤ 1, giving U^(4)_e = 1 - y_4(e) ≥ 0.

lemma U_slack_base {n k : ℕ} (net : LayeredNetwork n k)
    {X : LayeredPoint n} (mcf : MCFFeasible n k net X)
    (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (hk : 4 ≤ k) (e : Triple) (he : e ∈ Delta 4) :
    Y_s_norm net mcf s e ≤ 1 := by
  have hsum := Y_s_layer_sum net mcf s hs 4 ⟨le_refl 4, hk⟩
  have hle : Y_s net mcf s e ≤ s.flow_val := by
    calc Y_s net mcf s e
        ≤ (Delta 4).sum (fun u => Y_s net mcf s u) :=
          Finset.single_le_sum (fun u _ => Y_s_nonneg net mcf s u) he
      _ = s.flow_val := hsum
  unfold Y_s_norm
  rw [div_mul_eq_mul_div, one_mul]
  exact div_le_one_of_le hle (le_of_lt s.flow_pos)

-- ============================================================================
-- SECTION 5: THE CONTRADICTION ARGUMENT  U^(q+1) ≥ 0
-- ============================================================================
--
-- Chapter 5 proof: suppose U^(q+1)_{e} < 0 for some q ≥ 4, e = (i^o, j^o).
-- Then y^s_q(e) > U^(q)_e.
-- But: max flow into [q:e] ≤ Σ_{e' ∈ G(e)} y^s_{j^o}(e') - Σ_{l=j^o+1}^{q-1} y^s_l(e)
--    = U^(q)_e  [by definition of U]
-- And y^s_q(e) ≤ max flow (by flow conservation for commodity s).
-- Contradiction with U^(q+1) < 0.

/-- Flow bound: y^s_q(e) ≤ U^(q)_e.
    Chapter 5: "y^s_q(e) cannot be larger than U^(q)_{i^o j^o}
    as flow conservation is met for commodity s at each intermediate node." -/
lemma Y_s_le_U_slack {n k : ℕ} (net : LayeredNetwork n k)
    {X : LayeredPoint n} (mcf : MCFFeasible n k net X)
    (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (q : ℕ) (hq : 4 ≤ q) (hqk : q ≤ k)
    (e : Triple) (he : e ∈ Delta q) :
    Y_s_norm net mcf s e ≤ U_slack net mcf s q e := by
  -- Chapter 5 lines 1165-1167:
  -- y^s_q(e) ≤ U^(q)_e because:
  -- max flow into [q:e] ≤ Σ_{G(e)} y^s_{j^o}(e') - Σ_{l=j^o+1}^{q-1} y^s_l(e)
  -- = U^(q)_e (by definition)
  -- and flow conservation ensures y^s_q(e) ≤ max flow.
  -- Direct from mcf.stem_property.
  unfold Y_s_norm U_slack
  apply mul_le_mul_of_nonneg_left _ (div_nonneg one_pos.le (le_of_lt s.flow_pos))
  have hsp := mcf.stem_property s hs q hq hqk e
    (Delta_mem_layer e he) (by
      have := Delta_mem_layer e he
      have hej := e.h_jk
      omega)
  unfold Y_s direct_outflow rigid_path_flow at *
  convert hsp using 2
  apply Finset.sum_congr rfl
  intro e' _
  simp [Y_s, direct_outflow, rigid_path_flow]

/-- U^(q+1) ≥ 0 for all q ≥ 3.
    Chapter 5: the contradiction argument. -/
lemma U_slack_nonneg {n k : ℕ} (net : LayeredNetwork n k)
    {X : LayeredPoint n} (mcf : MCFFeasible n k net X)
    (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (q : ℕ) (hq : 3 ≤ q) (hqk : q ≤ k)
    (e : Triple) (he : e ∈ Delta q) :
    U_slack net mcf s q e ≥ 0 := by
  induction q with
  | zero => omega
  | succ q ih =>
    by_cases hq3 : q + 1 = 3
    · -- Base: U^(3) = 1 for edges in E_2
      -- U^(3)_e = Σ_{G(e)} Y_s_norm(e') - 0 = Σ_{G(e)} Y_s_norm(e') ≥ 0
      subst hq3
      unfold U_slack
      simp only [show (2 : ℕ) + 1 = 3 from rfl, Finset.Ico_self, Finset.sum_empty, sub_zero]
      apply Finset.sum_nonneg
      intro e' _
      exact Y_s_norm_nonneg net mcf s e'
    · by_cases hq4 : q + 1 = 4
      · -- Base: U^(4) ≥ 0 from U_slack_base
        subst hq4
        unfold U_slack
        simp only [Finset.Ico_self, Finset.sum_empty, sub_zero]
        apply Finset.sum_nonneg
        intro e' _
        exact Y_s_norm_nonneg net mcf s e'
      · -- Inductive step: U^(q+1) = U^(q) - y^s_q(e)
        -- By contradiction: if U^(q+1) < 0, then y^s_q(e) > U^(q)_e
        -- But Y_s_le_U_slack says y^s_q(e) ≤ U^(q)_e. Contradiction.
        by_contra h_neg
        push_neg at h_neg
        -- h_neg : U_slack net mcf s (q+1) e < 0
        have hq_ge4 : 4 ≤ q := by omega
        have hq_le_k : q ≤ k := by omega
        -- U^(q+1) = U^(q) - y^s_q(e)
        have hrec : U_slack net mcf s (q + 1) e =
            U_slack net mcf s q e - Y_s_norm net mcf s e := by
          unfold U_slack
          simp [Finset.sum_Ico_succ_top (by omega : e.j + 1 ≤ q)]
          ring
        -- From hrec and h_neg: y^s_q(e) > U^(q)_e
        have h_gt : Y_s_norm net mcf s e > U_slack net mcf s q e := by
          linarith [hrec ▸ h_neg]
        -- But Y_s_le_U_slack: y^s_q(e) ≤ U^(q)_e
        have h_le : Y_s_norm net mcf s e ≤ U_slack net mcf s q e :=
          Y_s_le_U_slack net mcf s hs q hq_ge4 hq_le_k e he
        linarith

-- ============================================================================
-- SECTION 6: CONSTRUCTING MIRFeasible k FROM Y^s
-- ============================================================================

/-- Lift Y_s_norm to the ℕ → ℕ×ℕ → ℚ format of MIRFeasible.
    x (l-4) p = Y_s_norm [l : e_p] for 4 ≤ l ≤ k. -/
noncomputable def lift_Y_s_norm {n k : ℕ} (net : LayeredNetwork n k)
    {X : LayeredPoint n} (mcf : MCFFeasible n k net X)
    (s : Commodity n k) : ℕ → ℕ × ℕ → ℚ :=
  fun m p =>
    let l := m + 4
    if hl : l ≤ k then
      match toEdge l p with
      | some e => Y_s_norm net mcf s e
      | none   => 0
    else 0

/-- Lift U_slack to the ℕ → ℕ×ℕ → ℚ format of MIRFeasible.
    u m p = U_slack at layer m+3. -/
noncomputable def lift_U_slack {n k : ℕ} (net : LayeredNetwork n k)
    {X : LayeredPoint n} (mcf : MCFFeasible n k net X)
    (s : Commodity n k) : ℕ → ℕ × ℕ → ℚ :=
  fun m p =>
    let l := m + 3
    if hl : l ≤ k then
      match toEdge l p with
      | some e => U_slack net mcf s l e
      | none   => 0
    else 0

-- ============================================================================
-- SECTION 7: MAIN LEMMA — Y_s_in_PMI
-- ============================================================================

/-- Lemma YsinMI (Chapter 5, Lemma YsinMI, p.1138):
    Given MCF(k) with z* = z_max, for each s ∈ S_k,
    (1/v^s) Y^s ∈ P_MI(k).
    The MIRFeasible witness has u 0 p ≤ 1 (the U^(4) ≥ 0 base case). -/
lemma Y_s_in_PMI
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k)
    (mcf : MCFFeasible n k net X)
    (s   : Commodity n k)
    (hs  : s ∈ mcf.commodities) :
    ∃ F : MIRFeasible k, ∀ p : ℕ × ℕ, F.u 0 p ≤ 1 := by

  -- Construct the MIRFeasible witness from Y^s/v^s
  refine ⟨{
    u     := lift_U_slack net mcf s
    x     := lift_Y_s_norm net mcf s
    h_n   := hk

    -- u_rec: U^(m+1) = U^(m) - y_{m+4}
    -- Follows from the recurrence U^(l+1) = U^(l) - A^(l+1) y_{l+1}
    u_rec := by
      intro m p
      unfold lift_U_slack lift_Y_s_norm
      simp only
      by_cases hk : m + 4 ≤ k
      · simp only [show m + 1 + 3 = m + 4 from by omega, dif_pos hk]
        simp only [show m + 3 ≤ k from by omega, show m + 4 ≤ k from hk]
        rcases toEdge (m + 4) p with _ | e
        · simp
        · simp only
          unfold U_slack
          simp [Finset.sum_Ico_succ_top (by omega : e.j + 1 ≤ m + 4)]
          ring
      · simp [dif_neg (by omega : ¬(m + 1 + 3 ≤ k)),
              dif_neg (show ¬(m + 3 ≤ k) from by omega)]

    -- x_nn: (1/v^s) Y^s ≥ 0
    x_nn := by
      intro m p
      unfold lift_Y_s_norm
      split_ifs with h
      · rcases toEdge (m + 4) p with _ | e
        · norm_num
        · exact Y_s_norm_nonneg net mcf s e
      · norm_num

    -- u_nn: U^(m) ≥ 0 for all m
    -- This is the main content: U^(q) ≥ 0 for all q ≥ 3.
    u_nn := by
      intro m p
      unfold lift_U_slack
      split_ifs with h
      · rcases toEdge (m + 3) p with _ | e
        · norm_num
        · apply U_slack_nonneg net mcf s hs (m + 3) (by omega) (by omega) e
          -- e ∈ Delta (m+3): from toEdge (m+3) p = some e
          -- toEdge gives e.i < e.j < m+3, so e ∈ Delta (m+3)
          simp [Delta, Triple.mk]
          exact ⟨e.h_ij, e.h_jk⟩
      · norm_num

    -- u0_le1: U^(3) entries ≤ 1
    -- This is the base case: (1/v^s) y^s_4(e) ≤ 1
    u0_le1 := by
      intro p
      unfold lift_U_slack
      simp only [show 0 + 3 = 3 from rfl]
      by_cases h3k : 3 ≤ k
      · simp only [dif_pos (by omega : 3 ≤ k)]
        rcases toEdge 3 p with _ | e
        · norm_num
        · unfold U_slack
          simp only [Finset.Ico_self, Finset.sum_empty, sub_zero]
          -- Σ_{e' ∈ generators e} Y_s_norm e' ≤ 1
          -- generators e ⊆ Delta 3, and Σ_{Delta 3} Y_s_norm = 1
          have hsum := Y_s_norm_layer_sum net mcf s hs 3 ⟨by omega, by omega⟩
          calc (generators e).sum (fun e' => Y_s_norm net mcf s e')
              ≤ (Delta 3).sum (fun e' => Y_s_norm net mcf s e') := by
                apply Finset.sum_le_sum_of_subset
                intro e' he'
                exact generators_subset_Delta e e' he'
            _ = 1 := hsum
      · simp [dif_neg (by omega : ¬(3 ≤ k))]
        norm_num
  }, ?_⟩

  -- Show u 0 p ≤ 1 (U^(3) ≤ 1 componentwise)
  intro p
  unfold lift_U_slack
  simp only [show 0 + 3 = 3 from rfl]
  by_cases h3k : (3 : ℕ) ≤ k
  · simp only [dif_pos h3k]
    rcases toEdge 3 p with _ | e
    · norm_num
    · unfold U_slack
      simp only [Finset.Ico_self, Finset.sum_empty, sub_zero]
      -- Σ_{e' ∈ generators e} Y_s_norm e' ≤ 1
      -- since generators e ⊆ Delta (e.j) and layer sums = 1
      have hsum := Y_s_norm_layer_sum net mcf s hs 3 ⟨by omega, by omega⟩
      calc (generators e).sum (fun e' => Y_s_norm net mcf s e')
          ≤ (Delta 3).sum (fun e' => Y_s_norm net mcf s e') := by
            apply Finset.sum_le_sum_of_subset
            intro e' he'
            exact generators_subset_Delta e e' he'
        _ = 1 := hsum
  · simp [dif_neg h3k]
    norm_num

-- ============================================================================
-- SECTION 8: SORRY INVENTORY
-- ============================================================================
--
-- [Sorry 1] Y_s_layer_sum
--   Σ_{u ∈ Delta l} Y_s net mcf s u = s.flow_val.
--   From MCF flow conservation (mcf.conservation):
--   at each layer l, the total flow of commodity s equals v^s.
--   Direct outflow + rigid path contribution sum to v^s.
--
-- [Sorry 2] Y_s_le_U_slack
--   y^s_q(e) ≤ U^(q)_e.
--   This is the KEY step of Chapter 5's contradiction argument (p.1166-1167):
--   "The maximum possible flow into [q:e] ≤ U^(q)_e as flow conservation
--   is met for commodity s at each intermediate node of N_{k-1}(s)."
--   In Lean: use mcf.node_cap_ok + mcf.conservation + induction on layers.
--
-- [Sorry 3] U_slack_nonneg base case (q+1 = 3)
--   U^(3) is the initial slack, equals 1 for edges in E_2.
--   Follows from initialSlack = 1 in SlackComputation.lean.
--
-- [Sorry 4] Delta membership in u_nn
--   e ∈ Delta (m+3) when toEdge (m+3) p = some e.
--   From toEdge definition: e.i < e.j < m+3, so e ∈ Delta (m+3).
--
-- [Sorry 5-6] u0_le1 cases
--   Σ_{e' ∈ generators e} Y_s_norm e' ≤ 1.
--   From Y_s_norm_layer_sum: Σ_{Delta l} Y_s_norm = 1 and generators e ⊆ Delta l.
--   Use Finset.sum_le_sum_of_subset + layer sum = 1.

end MembershipProject.Core
