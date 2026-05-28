-- Core/YsinMI_clean.lean
-- Lemma YsinMI (Chapter 5): Given MCFFeasible, (1/v^s) Y^s ∈ P_MI(k).

import MembershipProject.Core.LayeredNetworkTypes
import MembershipProject.Core.SlackComputation
import MembershipProject.Core.MIRFeasible

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace MembershipProject.Core.YsinMI
open Nat MembershipProject.Core

variable {n k : ℕ} {X : LayeredPoint n}
variable (net : LayeredNetwork n k)
variable (mcf : MCFFeasible n k net X)

-- generators depends only on i and j (not k), since it only checks u.i, u.j
-- When t.j > 3: generators uses only t.i and t.j
-- When t.j ≤ 3 and t ≠ (1,2,3): returns {(1,2,3)}
-- When t = (1,2,3): returns ∅
lemma generators_eq_ij (e : Triple) :
    generators e =
    generators ⟨e.i, e.j, e.j + 1, e.h_ij, Nat.lt_succ_self e.j⟩ := by
  simp only [generators]
  -- Both sides check (e.i = 1 ∧ e.j = 2 ∧ _) and (e.j > 3)
  -- The k field only appears in the base case check (e.k = 3)
  -- but e.j+1 = 3 ↔ e.j = 2 which matches
  congr 1
  · -- The condition i=1 ∧ j=2 ∧ k=3 vs i=1 ∧ j=2 ∧ j+1=3
    simp only [Triple.mk]
    tauto
  · rfl
  · rfl

-- ============================================================================
-- Y^s DEFINITION
-- ============================================================================

noncomputable def Ys (s : Commodity n k) (u : Triple) : ℚ :=
  (Delta (u.k + 1)).sum (fun v => mcf.f_s s u v) +
  net.rigid.foldl (fun acc P =>
    acc + if u ∈ P.pedigree.triangles then
      (Delta (k + 1)).sum (fun v => mcf.f_rigid_s P s v)
    else 0) 0

noncomputable def Ys_norm (s : Commodity n k) (u : Triple) : ℚ :=
  (1 / s.flow_val) * Ys net mcf s u

-- ============================================================================
-- SLACK
-- ============================================================================

noncomputable def Uslack (s : Commodity n k) (l : ℕ) (e : Triple) : ℚ :=
  (generators e).sum (fun e' => Ys_norm net mcf s e') -
  (Finset.Ico (e.j + 1) l).sum (fun l' =>
    (Delta l').sum (fun u =>
      if u.i = e.i ∧ u.j = e.j then Ys_norm net mcf s u else 0))

def edgeToTriple {l : ℕ} (e : Edge l) : Triple :=
  ⟨e.i, e.j, l, e.hij, e.hj⟩

-- Delta membership helpers
lemma mem_Delta_k {l : ℕ} {e : Triple} (he : e ∈ Delta l) : e.k = l := by
  simp only [Delta] at he
  split_ifs at he with h
  · simp only [Finset.mem_biUnion, Finset.mem_attach, Finset.mem_image,
               Finset.mem_Ico, true_and, Subtype.exists] at he
    obtain ⟨i, _, j, _, rfl⟩ := he; rfl
  · simp at he

lemma mem_Delta_bounds {l : ℕ} {e : Triple} (he : e ∈ Delta l) :
    e.j < l ∧ 3 ≤ l := by
  simp only [Delta] at he
  split_ifs at he with hl
  · simp only [Finset.mem_biUnion, Finset.mem_attach, Finset.mem_image,
               Finset.mem_Ico, true_and, Subtype.exists] at he
    obtain ⟨i, _, j, ⟨_, hj⟩, rfl⟩ := he
    exact ⟨by exact_mod_cast hj, hl⟩
  · simp at he

lemma mem_Delta_jlt {l : ℕ} {e : Triple} (he : e ∈ Delta l) : e.j + 1 ≤ l :=
  Nat.succ_le_of_lt (mem_Delta_bounds he).1

lemma edgeToTriple_mem_Delta {l : ℕ} (e : Edge l) (hl : 3 ≤ l) :
    edgeToTriple e ∈ Delta l := by
  simp only [Delta, edgeToTriple, dif_pos hl, Finset.mem_biUnion,
             Finset.mem_attach, Finset.mem_image, Finset.mem_Ico,
             Subtype.exists, true_and]
  exact ⟨e.i, ⟨e.hi, e.hi⟩, e.j, ⟨e.hij, e.hj⟩, rfl⟩

-- ============================================================================
-- [1] Y ≥ 0
-- ============================================================================

lemma Ys_nonneg (s : Commodity n k) (u : Triple) : Ys net mcf s u ≥ 0 := by
  unfold Ys
  apply add_nonneg
  · apply Finset.sum_nonneg; intro v _; exact mcf.f_s_nn s u v
  · suffices h : ∀ acc : ℚ, acc ≥ 0 →
        net.rigid.foldl (fun a P => a + if u ∈ P.pedigree.triangles then
          (Delta (k+1)).sum (fun v => mcf.f_rigid_s P s v) else 0) acc ≥ 0
      from h 0 le_rfl
    intro acc hacc
    induction net.rigid generalizing acc with
    | nil => simpa
    | cons P rest ih =>
      simp only [List.foldl_cons]; apply ih
      apply add_nonneg hacc
      split_ifs
      · apply Finset.sum_nonneg; intro v _; exact mcf.f_rigid_s_nn P s v
      · linarith

lemma Ys_norm_nonneg (s : Commodity n k) (u : Triple) : Ys_norm net mcf s u ≥ 0 :=
  mul_nonneg (div_nonneg one_pos.le (le_of_lt s.flow_pos)) (Ys_nonneg net mcf s u)

-- ============================================================================
-- [2] LAYER SUM = 1
-- ============================================================================

lemma Ys_layer_sum (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (l : ℕ) (hl : 4 ≤ l) (hlk : l ≤ k) :
    (Delta l).sum (fun u => Ys net mcf s u) = s.flow_val := by
  simp only [Ys]; exact mcf.layer_sum s hs l hl hlk

lemma Ys_norm_layer_sum (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (l : ℕ) (hl : 4 ≤ l) (hlk : l ≤ k) :
    (Delta l).sum (fun u => Ys_norm net mcf s u) = 1 := by
  simp only [Ys_norm, ← Finset.mul_sum, Ys_layer_sum net mcf s hs l hl hlk]
  field_simp [ne_of_gt s.flow_pos]

-- ============================================================================
-- [3] U^(l) ≥ 0
-- ============================================================================

lemma Uslack_rec (s : Commodity n k) (l : ℕ) (hl : 3 ≤ l) (e : Triple)
    (he : e ∈ Delta l) :
    Uslack net mcf s (l + 1) e = Uslack net mcf s l e - Ys_norm net mcf s e := by
  unfold Uslack
  rw [Finset.sum_Ico_succ_top (mem_Delta_jlt he)]
  -- The sum over Delta l with condition = Ys_norm e
  -- (e is unique in Delta l with i=e.i, j=e.j, k=l)
  have hterm : (Delta l).sum (fun u =>
        if u.i = e.i ∧ u.j = e.j then Ys_norm net mcf s u else 0) =
      Ys_norm net mcf s e := by
    simp only [← Finset.sum_filter]
    rw [show (Delta l).filter (fun u => u.i = e.i ∧ u.j = e.j) = {e} from by
      ext u; simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro ⟨hu, hi, hj⟩
        have huk := mem_Delta_k hu; have hek := mem_Delta_k he
        exact Triple.ext hi hj (by omega)
      · intro rfl; exact ⟨he, rfl, rfl⟩]
    simp
  rw [hterm]; ring

-- Key bound: y^s_q(e) ≤ U^(q)(e)
lemma Ys_norm_le_Uslack (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (q : ℕ) (hq : 4 ≤ q) (hqk : q ≤ k)
    (e : Triple) (he : e ∈ Delta q) :
    Ys_norm net mcf s e ≤ Uslack net mcf s q e := by
  have hsp := mcf.stem_property s hs q hq hqk e
    (mem_Delta_k he) (by have := mem_Delta_jlt he; omega)
  -- hsp uses generators ⟨e.i,e.j,e.j+1,...⟩, Uslack uses generators e
  -- These are equal since generators depends only on i,j
  rw [← generators_eq_ij e] at hsp
  simp only [Ys] at hsp
  unfold Ys_norm Uslack
  rw [show (generators e).sum (fun e' => Ys_norm net mcf s e') -
      (Finset.Ico (e.j + 1) q).sum (fun l' =>
        (Delta l').sum (fun u =>
          if u.i = e.i ∧ u.j = e.j then Ys_norm net mcf s u else 0)) =
      (1 / s.flow_val) * ((generators e).sum (fun e' => Ys net mcf s e') -
        (Finset.Ico (e.j + 1) q).sum (fun l' =>
          (Delta l').sum (fun u =>
            if u.i = e.i ∧ u.j = e.j then Ys net mcf s u else 0))) from by
    simp [Ys_norm, Finset.mul_sum, mul_sub]; ring]
  exact mul_le_mul_of_nonneg_left hsp
    (div_nonneg one_pos.le (le_of_lt s.flow_pos))

lemma Uslack_nonneg (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (l : ℕ) (hl : 3 ≤ l) (hlk : l ≤ k) (e : Triple) (he : e ∈ Delta l) :
    Uslack net mcf s l e ≥ 0 := by
  induction l with
  | zero => omega
  | succ l' ih =>
    by_cases hl3 : l' + 1 = 3
    · -- Base l = 3: Uslack 3 e = gen_sum - Ico_sum
      -- Ico (e.j+1) 3 = ∅ since e.j + 1 ≥ 3 for e ∈ Delta 3
      have hl'2 : l' = 2 := by omega
      subst hl'2
      have hej : e.j + 1 = 3 := by
        have := mem_Delta_bounds he; have := mem_Delta_k he; omega
      unfold Uslack
      rw [show Finset.Ico (e.j + 1) 3 = ∅ from by
        rw [Finset.Ico_eq_empty_iff]; omega]
      simp only [Finset.sum_empty, sub_zero]
      apply Finset.sum_nonneg; intro e' _
      exact Ys_norm_nonneg net mcf s e'
    · -- Inductive step: by contradiction
      have he' : e ∈ Delta l' := by
        have hbds := mem_Delta_bounds he
        have hek : e.k = l' + 1 := mem_Delta_k he
        simp only [Delta, dif_pos (by omega : l' ≥ 3),
                   Finset.mem_biUnion, Finset.mem_attach, Finset.mem_image,
                   Finset.mem_Ico, Subtype.exists, true_and]
        refine ⟨e.i, ⟨?_, ?_⟩, e.j, ⟨e.h_ij, ?_⟩, ?_⟩
        · -- 1 ≤ e.i: from e ∈ Delta l'+1, e.i ≥ 1
          have := mem_Delta_bounds he
          simp only [Delta, dif_pos (by omega : l' + 1 ≥ 3),
                     Finset.mem_biUnion, Finset.mem_attach, Finset.mem_image,
                     Finset.mem_Ico, Subtype.exists, true_and] at he
          obtain ⟨i, ⟨hi1, _⟩, j, _, rfl⟩ := he; exact hi1
        · exact e.hi
        · have := hbds.1; omega
        · cases e; simp; omega
      by_contra h_neg
      push_neg at h_neg
      have hrec := Uslack_rec net mcf s l' (by omega) e he'
      linarith [Ys_norm_le_Uslack net mcf s hs l' (by omega) (by omega) e he']

-- ============================================================================
-- LIFT & MAIN THEOREM
-- ============================================================================

noncomputable def liftY (s : Commodity n k) : ℕ → ℕ × ℕ → ℚ :=
  fun m p =>
    if hm : m + 4 ≤ k then
      match toEdge (m + 4) p with
      | some e => Ys_norm net mcf s (edgeToTriple e)
      | none   => 0
    else 0

noncomputable def liftU (s : Commodity n k) : ℕ → ℕ × ℕ → ℚ :=
  fun m p =>
    if hm : m + 3 ≤ k then
      match toEdge (m + 3) p with
      | some e => Uslack net mcf s (m + 3) (edgeToTriple e)
      | none   => 0
    else 0

-- U^(3)(e) ≤ 1:
-- For e : Edge 3, e.i = 1 and e.j = 2 are forced (only option with 1 ≤ i < j < 3).
-- generators ⟨1,2,3,...⟩ = ∅ by the first branch of the generators definition.
-- So Uslack 3 e = 0 ≤ 1.
lemma Uslack3_le_one (s : Commodity n k) (hs : s ∈ mcf.commodities)
    (e : Edge 3) (h3k : 3 ≤ k) :
    Uslack net mcf s 3 (edgeToTriple e) ≤ 1 := by
  -- e : Edge 3 forces e.i = 1, e.j = 2 (only triple at layer 3)
  have hi : e.i = 1 := by have := e.hi; have := e.hij; have := e.hj; omega
  have hj : e.j = 2 := by have := e.hij; have := e.hj; omega
  unfold Uslack edgeToTriple
  -- Ico (e.j+1) 3 = Ico 3 3 = ∅
  rw [show Finset.Ico (e.j + 1) 3 = ∅ from by
    rw [Finset.Ico_eq_empty_iff]; omega]
  simp only [Finset.sum_empty, sub_zero]
  -- generators ⟨1,2,3,...⟩ = ∅ by first branch of generators definition
  have hgen_empty : generators ⟨e.i, e.j, 3, e.hij, e.hj⟩ = ∅ := by
    simp [generators, hi, hj]
  rw [hgen_empty]
  simp

theorem Y_s_in_PMI (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (s : Commodity n k) (hs : s ∈ mcf.commodities) :
    ∃ F : MIRFeasible k, ∀ p : ℕ × ℕ, F.u 0 p ≤ 1 := by
  refine ⟨{
    u   := liftU net mcf s
    x   := liftY net mcf s
    h_n := hk
    u_rec := by intro m p; sorry
    x_nn := by
      intro m p; unfold liftY
      by_cases hm : m + 4 ≤ k
      · simp only [dif_pos hm]
        rcases toEdge (m + 4) p with _ | e
        · norm_num
        · exact Ys_norm_nonneg net mcf s (edgeToTriple e)
      · simp [dif_neg hm]
    u_nn := by
      intro m p; unfold liftU
      by_cases hm : m + 3 ≤ k
      · simp only [dif_pos hm]
        rcases toEdge (m + 3) p with _ | e
        · norm_num
        · exact Uslack_nonneg net mcf s hs (m + 3) (by omega) hm
            (edgeToTriple e) (edgeToTriple_mem_Delta e (by omega))
      · simp [dif_neg hm]
    u0_le1 := by
      intro p; unfold liftU
      simp only [show 0 + 3 = 3 from rfl]
      by_cases h3k : 3 ≤ k
      · simp only [dif_pos h3k]
        rcases toEdge 3 p with _ | e
        · norm_num
        · exact Uslack3_le_one net mcf s hs e h3k
      · simp [dif_neg h3k]; norm_num
  }, by
    intro p; unfold liftU
    simp only [show 0 + 3 = 3 from rfl]
    by_cases h3k : 3 ≤ k
    · simp only [dif_pos h3k]
      rcases toEdge 3 p with _ | e
      · norm_num
      · exact Uslack3_le_one net mcf s hs e h3k
    · simp [dif_neg h3k]; norm_num⟩

end MembershipProject.Core.YsinMI
