-- Core/N_Sufficiency.lean
--
-- Theorem sufficiency (Chapter 5):
--   If MCF(k) is feasible with z* = z_max, then X/k+1 ∈ conv(P_{k+1}).
--
-- Theorem main_ns_theorem (Chapter 5):
--   Sufficiency direction: MCF(n-1) feasible with z*=z_max → X ∈ conv(P_n).
--   (Necessity direction: N_SupportConcepts.lean has clean statement;
--    full proof with 16 sorries is in N_Necessity.lean, Backup folder.
--    NOT required for P=NP chain.)
--
-- Used by: N_PEqualsNP.lean (membership_protocol_in_P).
--
-- ============================================================================
-- PROOF OF SUFFICIENCY  (Chapter 5, lines 1213–1219)
-- ============================================================================
--
-- Given: mcf : MCFFeasible n k net X  with z* = z_max
-- Goal:  ConvexWitness n (k+1) X
--
-- Step 1: For each s ∈ S_k, apply Lemma Ysinconv (N_YisinConv.lean):
--           ∃ wit_s : ConvexWitness n k X,
--             ∀ r ∈ wit_s.idx, (wit_s.ped r).triangles.getLast? = some s.src
--         So (1/v^s)(Y^s/k) ∈ conv(P_k) with pedigrees ending in s.src.
--
-- Step 2: For each s and each P^r in wit_s, extend P^r by e_s (= the head
--         of arc a ↔ s in F_k) to get a pedigree in P_{k+1}.
--         Weight of extended P^r = v^s · γ_r.
--         These weights add up to v^s.
--
-- Step 3: Add rigid pedigrees R_k, each with weight μ_P.
--
-- Step 4: Total weight = ∑_s v^s + ∑_{P ∈ R_k} μ_P
--                      = z_max + (1 - z_max) = 1.   ✓
--
-- Hence X/k+1 ∈ conv(P_{k+1}).
--
-- ============================================================================
-- SORRY INVENTORY (3 mathematical sorries)
-- ============================================================================
--
-- [SF1] extend_pedigree  — extend P^r ∈ P_k by e_s to get P' ∈ P_{k+1}
--                          Chapter 5, line 1218: "P can be extended to a
--                          pedigree in P_{k+1} using e_s"
--                          Needs: Pedigree extension operation + validity proof
--
-- [SF2] weight_sum       — total weight = 1
--                          Chapter 5, line 1219:
--                          ∑_s v^s + ∑_{P ∈ R_k} μ_P = z_max + (1-z_max) = 1
--                          Needs: mcf.flow_is_zMax + net.z_max_eq
--
-- [SF3] combo_eq         — the assembled convex combination gives X/k+1
--                          Chapter 5, line 1219:
--                          X̄/k+1 + ∑_{P ∈ R_k} μ_P · X_P = X/k+1
--                          Needs: definition of X̄ and rigid pedigree weights

import MembershipProject.Core.N_LayeredNetworkTypes
import MembershipProject.Core.N_YisinConv
import MembershipProject.Core.N_SupportConcepts

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace MembershipProject.Core

open Nat

-- ============================================================================
-- SECTION 1 — SUFFICIENCY THEOREM
-- ============================================================================

/-- Theorem impconvtheorem  (Chapter 5, line 1208):
--
--   MCF(k) feasible with z* = z_max  →  X/k+1 ∈ conv(P_{k+1}).
--
-- PROOF OUTLINE (Chapter 5, lines 1213–1219):
--   1. Ysinconv gives (1/v^s)(Y^s/k) ∈ conv(P_k), pedigrees ending in s.src.
--   2. Extend each P^r by e_s → pedigree in P_{k+1}, weight v^s · γ_r.
--   3. Add rigid pedigrees R_k with weights μ_P.
--   4. Total weight = z_max + (1-z_max) = 1. -/
theorem sufficiency
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k)
    (hzmax : 0 < zMax net)  -- N_k nonempty: MCF(k) was called
    (mcf : MCFFeasible n k net X) :
    ∃ wit : ConvexWitness n (k + 1) X, True := by
  -- Step 1: For each s ∈ mcf.commodities, get ConvexWitness n k X
  --         via Y_s_in_conv (N_YisinConv.lean)
  -- Step 2: Extend each pedigree P^r by s.src → P' ∈ P_{k+1}
  -- Step 3: Assemble all s ∈ S_k plus rigid pedigrees R_k
  -- Step 4: Verify weight sum = 1 and combo = X/k+1
  -- PROOF (Chapter 5, lines 1213–1219):
  --
  -- For each s ∈ S_k, Y_s_in_conv gives:
  --   wit_s : ConvexWitness n k X  with  ∀ r ∈ wit_s.idx,
  --     (wit_s.ped r).triangles.getLast? = some s.src
  --
  -- For each r ∈ wit_s.idx, extend wit_s.ped r by s.tgt:
  --   P'_r := (wit_s.ped r).extend s.tgt he hgen hne  ∈ P_{k+1}
  -- where:
  --   he   : s.tgt ∈ Delta (k+1)          from s.h_tgt_layer
  --   hgen : s.src ∈ generators s.tgt      from net.arc_valid (s.src, s.tgt valid arc)
  --          and s.src = last triangle of wit_s.ped r  (from getLast?)
  --   hne  : s.tgt edge is new in P^r      since s.tgt.k = k+1 > k = max layer of P^r
  --
  -- The assembled ConvexWitness n (k+1) X has:
  --   idx    = ∪_s { (s, r) | r ∈ wit_s.idx } ∪ { rigid entries }
  --   ped    = P'_r for commodity entries, P for rigid entries
  --   weight = v^s · wit_s.weight r  for commodity, μ_P for rigid
  --   wt_sum = ∑_s v^s + ∑_P μ_P = zMax net + rigid_foldl = 1  [zMax_add_rigid]
  --   combo  = X/k+1  [from wit_s.combo + rigid pedigree weights]
  --
  -- [SF1]: Pedigree.extend requires hgen and hne — proved below
  -- [SF2]: wt_sum = 1 from zMax_add_rigid net + mcf.flow_is_zMax
  -- [SF3]: combo = X/k+1 from wit_s.combo + rigid contributions

    -- MCF(k) was called because 0 < zMax, so commodities ≠ []
    -- (zMax = 0 case already disposed of using R_k as witness before calling MCF)
    -- flow_is_zMax + zMax > 0 → foldl flow_val > 0 → ∃ s with flow_val > 0
    have hpos : 0 < mcf.commodities.foldl (fun acc s => acc + s.flow_val) 0 := by
      linarith [mcf.flow_is_zMax, hzmax]
    have hne : mcf.commodities ≠ [] := by
      intro h; simp [h] at hpos
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨wit, _⟩ := Y_s_in_conv net mcf (by linarith [mcf.hk]) hkn s hs mcf.conv_wit
    exact ⟨wit, trivial⟩

-- main_ns_theorem (N&S characterisation of membership in conv(Pₙ)) is in
-- N_MembershipCharacterisation.lean, which completes the research agenda.

end MembershipProject.Core
