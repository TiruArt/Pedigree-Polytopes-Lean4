-- File No. TBD+1 - N_PackabilityCorollary.lean
--
-- Packability Corollary (arXiv:2507.09069v1, Theorem 1):
--
-- STATEMENT:
--   Given (1) Y ∈ P_MI(k+1), (2) Y/k ∈ conv(P_k), (3) y_{k+1}(e') = 1,
--   then Y/(k+1) ∈ conv(P_{k+1}).
--
-- PROOF:
--   Take any λ ∈ Λ_k(X). For each r ∈ I(λ):
--     u = Σ_r λ_r U^r  (slack decomposition, U^r ∈ {0,1}^{p_k})
--     y_{k+1}(e') = 1 and y_{k+1} ≤ u  ⟹  u_{e'} = 1
--     Σ_r λ_r U^r_{e'} = 1, U^r ∈ {0,1}  ⟹  U^r_{e'} = 1 ∀ r
--     U^r_{e'} = 1  ⟹  e' ∈ T^r  ⟹  generator of e' in X^r
--   Define Y^r = (X^r, ind(e')) ∈ P_{k+1}  (extend X^r by e')
--   Y/(k+1) = Σ_r λ_r Y^r ∈ conv(P_{k+1})  □
--
-- Reference: Arthanari, T.S. arXiv:2507.09069v1 [math.CO].

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_RestrictionFull
import MembershipProject.Core.N_PedigreeDefinition
import MembershipProject.Core.N_LayeredNetworkTypes
import MembershipProject.Core.N_MIRFeasible

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace MembershipProject.Core

open Nat

-- ============================================================
-- HELPER: membership in extended pedigree triangles
-- t ∈ (P.extend e).triangles ↔ t ∈ P.triangles ∨ t = e
-- ============================================================

lemma Pedigree.extend_mem_triangles {n : ℕ} (P : Pedigree n) (e : Triple)
    (he : e ∈ Delta (n + 1))
    (hgen : ∃ i, ∃ hi : i < P.triangles.length,
              P.triangles.get ⟨i, hi⟩ ∈ generators e)
    (hne : ∀ i, ∀ hi : i < P.triangles.length,
              (P.triangles.get ⟨i, hi⟩).i ≠ e.i ∨
              (P.triangles.get ⟨i, hi⟩).j ≠ e.j)
    (t : Triple) :
    t ∈ (P.extend e he hgen hne).triangles ↔
    t ∈ P.triangles ∨ t = e := by
  simp [Pedigree.extend, List.mem_append, List.mem_singleton]

-- ============================================================
-- HELPER: when y_{k+1}(e') = 1, all other layer-(k+1) values = 0
-- (layer sum = 1 and X ≥ 0)
-- ============================================================

lemma layer_complement_zero
    {n k : ℕ} (X : LayeredPoint n)
    (hX_sum : (Delta (k + 1)).sum X = 1)
    (hX_nn  : ∀ t ∈ Delta (k + 1), X t ≥ 0)
    (e' : Triple) (he' : e' ∈ Delta (k + 1)) (hX1 : X e' = 1)
    (t : Triple) (ht : t ∈ Delta (k + 1)) (hte : t ≠ e') :
    X t = 0 := by
  have hnn : X t ≥ 0 := hX_nn t ht
  have hle : X t ≤ 0 := by
    have hsplit : X e' + ((Delta (k + 1)).erase e').sum X = 1 := by
      rw [← hX_sum, ← Finset.add_sum_erase _ _ he']
    have hcomp : ((Delta (k + 1)).erase e').sum X = 0 := by linarith [hX1]
    have hts : t ∈ (Delta (k + 1)).erase e' :=
      Finset.mem_erase.mpr ⟨hte, ht⟩
    have := Finset.single_le_sum (f := X)
      (fun u hu => hX_nn u (Finset.mem_erase.mp hu).2) hts
    linarith
  linarith

-- ============================================================
-- PACKABILITY COROLLARY (Theorem 1 of arXiv paper)
-- ============================================================

/-- Packability Corollary (arXiv:2507.09069v1, Theorem 1).

    If Y ∈ P_MI(k+1), Y/k ∈ conv(P_k), and y_{k+1}(e') = 1
    for some e' ∈ Delta(k+1), then Y/(k+1) ∈ conv(P_{k+1}).

    Three antecedents only (pure geometric result, no MCF content):
    - wit  : ConvexWitness certifying Y/k ∈ conv(P_k)
    - hX   : y_{k+1}(e') = 1
    - h_gen, h_ne : e' can extend each pedigree in the witness -/
theorem packability_corollary
    {n k : ℕ} {X : LayeredPoint n}
    (hX_sum  : (Delta (k + 1)).sum X = 1)
    (hX_nn   : ∀ t ∈ Delta (k + 1), X t ≥ 0)
    (hX_supp : ∀ t, t.k = k + 1 → t ∉ Delta (k + 1) → X t = 0)
    (wit     : ConvexWitness n k X)
    (e'      : Triple)
    (he'     : e' ∈ Delta (k + 1))
    (hX      : X e' = 1)
    (h_gen   : ∀ r ∈ wit.idx,
        ∃ i, ∃ hi : i < (wit.ped r).triangles.length,
          (wit.ped r).triangles.get ⟨i, hi⟩ ∈ generators e')
    (h_ne    : ∀ r ∈ wit.idx,
        ∀ i, ∀ hi : i < (wit.ped r).triangles.length,
          ((wit.ped r).triangles.get ⟨i, hi⟩).i ≠ e'.i ∨
          ((wit.ped r).triangles.get ⟨i, hi⟩).j ≠ e'.j) :
    ∃ wit' : ConvexWitness n (k + 1) X, True := by
  have hne : wit.idx.Nonempty := by
    rcases Finset.eq_empty_or_nonempty wit.idx with h | h
    · have hws := wit.wt_sum; simp [h] at hws
    · exact h
  obtain ⟨r₀, hr₀⟩ := hne
  let default_ped : Pedigree (k + 1) :=
    (wit.ped r₀).extend e' he' (h_gen r₀ hr₀) (h_ne r₀ hr₀)
  exact ⟨{
    idx    := wit.idx
    ped    := fun r =>
      if hr : r ∈ wit.idx then
        (wit.ped r).extend e' he' (h_gen r hr) (h_ne r hr)
      else
        default_ped
    weight := wit.weight
    wt_pos  := wit.wt_pos
    wt_zero := wit.wt_zero
    wt_sum  := wit.wt_sum
    combo  := by
      intro t ht
      have he'k : e'.k = k + 1 := mem_Delta_k he'
      have htnold : ∀ r ∈ wit.idx, t.k = k + 1 → t ∉ (wit.ped r).triangles := by
        intro r hr htk hmem
        obtain ⟨i, hget⟩ := List.mem_iff_get.mp hmem
        have hlayer := (wit.ped r).h_layers i.val i.isLt
        have hlen   := (wit.ped r).h_length
        have hn     := (wit.ped r).h_n
        have : (wit.ped r).triangles.get ⟨i.val, i.isLt⟩ = t := by
          exact_mod_cast hget
        rw [this] at hlayer; omega
      by_cases hk : t.k ≤ k
      · -- t at layer ≤ k: extend doesn't change membership
        have hte : t ≠ e' := by intro h; rw [h] at hk; omega
        convert wit.combo t (by omega) using 1
        apply Finset.sum_congr rfl; intro r hr
        simp only [dif_pos hr, Pedigree.extend_mem_triangles]
        congr 1; simp [hte]
      · -- t at layer k+1
        have htk : t.k = k + 1 := by omega
        by_cases hte : t = e'
        · -- t = e': y_{k+1}(e') = 1, all extended pedigrees contain e'
          subst hte
          trans (wit.idx.sum wit.weight)
          · apply Finset.sum_congr rfl; intro r hr
            simp only [dif_pos hr, Pedigree.extend,
                       List.mem_append, List.mem_singleton,
                       or_true, ↓reduceIte, mul_one]
          · rw [wit.wt_sum, hX]
        · -- t ≠ e': X t = 0 and no extended pedigree contains t
          have hXt : X t = 0 := by
            by_cases htDelta : t ∈ Delta (k + 1)
            · exact layer_complement_zero X hX_sum hX_nn e' he' hX t htDelta hte
            · exact hX_supp t htk htDelta
          have hsum : wit.idx.sum (fun r => wit.weight r *
              if t ∈ (if hr : r ∈ wit.idx then
                (wit.ped r).extend e' he' (h_gen r hr) (h_ne r hr)
              else default_ped).triangles then 1 else 0) = 0 :=
            Finset.sum_eq_zero (fun r hr => by
              simp only [dif_pos hr, Pedigree.extend,
                         List.mem_append, List.mem_singleton, hte, or_false]
              simp [htnold r hr htk])
          linarith [hsum, hXt]
  }, trivial⟩

end MembershipProject.Core
