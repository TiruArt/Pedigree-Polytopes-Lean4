-- Core/N_YisinConv.lean
--
-- Lemma Ysinconv (Chapter 5, Theorem 1 / Packability Corollary):
--
--   Given X ∈ P_MI(k+1), X/k ∈ conv(P_k), x_{k+1}(arc_head) = 1,
--   then X/(k+1) ∈ conv(P_{k+1}).
--
-- PROOF: Direct application of packability_corollary.
--   1. X ∈ P_MI(k+1)         — Y_s_in_PMI
--   2. X/k ∈ conv(P_k)       — hwit
--   3. X s.arc_head = 1      — mcf.src_val

import MembershipProject.Core.N_LayeredNetworkTypes
import MembershipProject.Core.N_MIRFeasible
import MembershipProject.Core.N_PedigreeDefinition
import MembershipProject.Core.N_YisinMI
import MembershipProject.Core.N_PackabilityCorollary

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace MembershipProject.Core

open Nat

theorem Y_s_in_conv
    {n k : ℕ} {X : LayeredPoint n}
    (net  : LayeredNetwork n k)
    (mcf  : MCFFeasible n k net X)
    (hk   : 5 ≤ k) (hkn : k + 1 ≤ n)
    (s    : Commodity n k)
    (hs   : s ∈ mcf.commodities)
    (hwit : ConvexWitness n k X) :
    ∃ wit : ConvexWitness n (k + 1) X, True := by
  have hX_nn  : ∀ t ∈ Delta (k + 1), X t ≥ 0 := fun t _ => mcf.X_nn t
  have hX_sum : (Delta (k + 1)).sum X = 1 :=
    mcf.X_layer_sum (k + 1) (by omega) (le_refl _)
  have hX_supp : ∀ t, t.k = k + 1 → t ∉ Delta (k + 1) → X t = 0 := by
    intro t htk htDelta
    have hnn := mcf.X_nn t
    rcases lt_or_eq_of_le hnn with h | h
    · exact absurd (net.node_valid t (mcf.pos_X_node t h)) (htk ▸ htDelta)
    · linarith
  have h_ne : ∀ r ∈ hwit.idx, ∀ i, ∀ hi : i < (hwit.ped r).triangles.length,
      ((hwit.ped r).triangles.get ⟨i, hi⟩).i ≠ s.arc_head.i ∨
      ((hwit.ped r).triangles.get ⟨i, hi⟩).j ≠ s.arc_head.j := by
    intro r hr i hi
    -- Establish layer bound: triangles[i].k = i+3 ≤ k < k+1
    have hlay  := (hwit.ped r).h_layers i hi
    have hlen  := (hwit.ped r).h_length
    have hn    := (hwit.ped r).h_n
    have hk2   : 2 ≤ k := by omega
    have hi'   : i < k - 2 := hlen ▸ hi
    have htk   : ((hwit.ped r).triangles.get ⟨i, hi⟩).k = i + 3 := hlay
    have htk_lt : ((hwit.ped r).triangles.get ⟨i, hi⟩).k < k + 1 := by
      simp only [Triple.k] at htk ⊢; omega
    -- X(triangles[i]) > 0 from combo + wt_pos
    have hXt : X ((hwit.ped r).triangles.get ⟨i, hi⟩) > 0 := by
      have hcombo := hwit.combo ((hwit.ped r).triangles.get ⟨i, hi⟩) (by
        simp only [Triple.k] at htk_lt ⊢; omega)
      have hmem : (hwit.ped r).triangles.get ⟨i, hi⟩ ∈ (hwit.ped r).triangles :=
        List.get_mem _ ⟨i, hi⟩
      have hnn : ∀ r' ∈ hwit.idx, 0 ≤ hwit.weight r' *
          if (hwit.ped r).triangles.get ⟨i, hi⟩ ∈ (hwit.ped r').triangles then 1 else 0 :=
        fun r' hr' => mul_nonneg (le_of_lt (hwit.wt_pos r' hr'))
          (by split_ifs <;> norm_num)
      have hpos : 0 < hwit.weight r *
          if (hwit.ped r).triangles.get ⟨i, hi⟩ ∈ (hwit.ped r).triangles then 1 else 0 := by
        simp only [hmem, if_true, mul_one]; exact hwit.wt_pos r hr
      linarith [Finset.single_le_sum hnn hr, hcombo]
    exact mcf.ext_new s hs _ (mcf.pos_X_node _ hXt) (by
      simp only [Triple.k] at htk_lt ⊢; omega)
  have h_gen : ∀ r ∈ hwit.idx, ∃ i, ∃ hi : i < (hwit.ped r).triangles.length,
      (hwit.ped r).triangles.get ⟨i, hi⟩ ∈ generators s.arc_head := by
    intro r hr
    have hsrc_gen : s.src ∈ generators s.arc_head :=
      net.arc_valid s.src s.arc_head (mcf.src_in_net s hs) (mcf.head_in_net s hs)
        (by have h1 := mem_Delta_k s.src_in_delta
            have h2 := mem_Delta_k s.head_in_delta
            simp only [Triple.k] at h1 h2 ⊢; omega)
    have hXsrc := mcf.src_node_val s hs
    have hcombo := hwit.combo s.src (le_of_eq (mem_Delta_k s.src_in_delta))
    rw [hXsrc] at hcombo
    have hmem : s.src ∈ (hwit.ped r).triangles := by
      by_contra h
      have hnn : ∀ r' ∈ hwit.idx,
          0 ≤ hwit.weight r' * if s.src ∈ (hwit.ped r').triangles then 1 else 0 :=
        fun r' hr' => mul_nonneg (le_of_lt (hwit.wt_pos r' hr'))
          (by split_ifs <;> norm_num)
      have hlt : hwit.idx.sum (fun r' =>
          hwit.weight r' * if s.src ∈ (hwit.ped r').triangles then 1 else 0) <
          hwit.idx.sum hwit.weight :=
        Finset.sum_lt_sum
          (fun r' hr' => by
            apply mul_le_of_le_one_right (le_of_lt (hwit.wt_pos r' hr'))
            split_ifs <;> norm_num)
          ⟨r, hr, by simp only [h, if_false, mul_zero]; exact hwit.wt_pos r hr⟩
      linarith [hwit.wt_sum, hcombo]
    obtain ⟨⟨i, hi⟩, heq⟩ := List.mem_iff_get.mp hmem
    exact ⟨i, hi, heq ▸ hsrc_gen⟩
  exact packability_corollary hX_sum hX_nn hX_supp hwit s.arc_head
    s.head_in_delta (mcf.src_val s hs) h_gen h_ne

end MembershipProject.Core
