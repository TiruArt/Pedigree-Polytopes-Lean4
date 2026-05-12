-- Core/N_Necessity.lean
--
-- Theorem imptheorem  (Chapter 5, Theorem imptheorem, line 1033):
--
--   Given X/k+1 ∈ conv(P_{k+1}), there exists a feasible solution
--   f, f^s to MCF(k) with z* = z_max.
--
-- ============================================================================
-- PROOF STRUCTURE  (Chapter 5, lines 1041–1094)
-- ============================================================================
--
-- Given: wit : ConvexWitness n (k+1) X  — witness for X/k+1 ∈ conv(P_{k+1})
-- Goal:  MCFFeasible n k net X          — feasible MCF(k) with z* = z_max
--
-- Construction (instant flow, Chapter 5 equations flowdef, f_sdef):
--
--   For arc a = (u, v) in N_k:
--     f_a = ∑_{r ∈ I(λ) | X^r ∥ a} λ_r
--         = ∑_{r ∈ wit.idx | u ∈ (wit.ped r).triangles
--                           ∧ v ∈ (wit.ped r).triangles} wit.weight r
--
--   For commodity s ∈ S_k, arc a ∈ N_{l-1}(s):
--     f^s_a = ∑_{r ∈ I_s(λ) | X^r ∥ a} λ_r
--           = ∑_{r ∈ wit.idx | s.src ∈ (wit.ped r).triangles
--                             ∧ u ∈ (wit.ped r).triangles
--                             ∧ v ∈ (wit.ped r).triangles} wit.weight r
--
-- Verification:
--   (1) f_s_nn    : wit.wt_pos → weights ≥ 0
--   (2) conservation: inflow = outflow = ∑_{r | x^r_l(e)=1} λ_r
--                     by the pedigree path property (each pedigree has
--                     exactly one triangle per layer)
--   (3) flow_vals : ∑_{v} f_s(s.src, v) = s.flow_val = v^s
--                   by wit.wt_sum restricted to I_s(λ)
--   (4) total_flow: ∑_s v^s = z_max  by wit.wt_sum + z_max definition
--
-- NOTE: InstantFlow.lean uses the old Triple API and cannot be imported.
-- The flow conservation argument is encoded directly from wit.combo.
--
-- ============================================================================
-- SORRY INVENTORY (3 mathematical sorries)
-- ============================================================================
--
-- [N1] conservation   — inflow = outflow at each intermediate node
--                       Each pedigree has exactly one triangle per layer,
--                       so X^r ∥ (u,v) and X^r ∥ (v,w) implies
--                       x^r_l(e) = 1 for the unique e at layer l.
--                       Chapter 5, lines 1071–1082.
--
-- [N2] flow_vals      — ∑_{Delta(k+1)} f_s(s.src, v) = s.flow_val
--                       wit.wt_sum restricted to I_s(λ) = wit.idx.
--                       Chapter 5, lines 1085–1089.
--
-- [N3] total_flow     — ∑_s v^s = z_max
--                       Chapter 5, line 1089.

import MembershipProject.Core.N_LayeredNetworkTypes
import MembershipProject.Core.N_YisinConv

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace MembershipProject.Core

open Nat

-- ============================================================================
-- SECTION 1 — THE INSTANT FLOW CONSTRUCTION
-- ============================================================================
--
-- For a ConvexWitness wit, the instant flow assigns to each arc (u,v)
-- the total weight of pedigrees that use BOTH u at layer u.k and v at layer v.k.

/-- Pedigrees in wit that use triple u at layer u.k.
    Paper §6: S_O(u) = { r ∈ I(λ) | X^r uses edge u }. -/
noncomputable def instantFlow_S_O {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X) (u : Triple) : Finset ℕ :=
  wit.idx.filter (fun r => u ∈ (wit.ped r).triangles)

/-- Pedigrees in wit that use both u and v (agree with arc (u,v)).
    Paper: I(λ) restricted to X^r ∥ (u,v). -/
noncomputable def instantFlow_arc {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X) (u v : Triple) : Finset ℕ :=
  (instantFlow_S_O wit u) ∩ (instantFlow_S_O wit v)

/-- The instant flow value on arc (u,v):
    f_{u,v} = ∑_{r ∈ I(λ), X^r ∥ (u,v)} λ_r.
    Chapter 5, equation flowdef. -/
noncomputable def f_instant {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X) (u v : Triple) : ℚ :=
  (instantFlow_arc wit u v).sum wit.weight

/-- The commodity-s instant flow on arc (u,v):
    f^s_{u,v} = ∑_{r ∈ I_s(λ), X^r ∥ (u,v)} λ_r
    where I_s(λ) = { r | X^r agrees with arc (s.src, s.tgt) designating s }
    i.e. both s.src and s.tgt appear in (ped r).triangles.
    X^r ∥ a means arc a = (s.src, s.tgt) is in the path of pedigree X^r.
    Chapter 5, equation f_sdef. -/
noncomputable def f_s_instant {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X) (s : Commodity n k) (u v : Triple) : ℚ :=
  (instantFlow_arc wit u v ∩
    wit.idx.filter (fun r => s.src ∈ (wit.ped r).triangles)).sum wit.weight

-- ============================================================================
-- SECTION 2 — NON-NEGATIVITY
-- ============================================================================

lemma f_instant_nn {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X) (u v : Triple) :
    f_instant wit u v ≥ 0 := by
  apply Finset.sum_nonneg
  intro r hr
  apply le_of_lt
  apply wit.wt_pos
  -- hr : r ∈ instantFlow_arc wit u v
  -- = r ∈ (wit.idx.filter (u ∈ ...)) ∩ (wit.idx.filter (v ∈ ...))
  have h1 := Finset.mem_inter.mp hr
  have h2 := (Finset.mem_filter.mp h1.1).1
  exact h2

lemma f_s_instant_nn {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X) (s : Commodity n k) (u v : Triple) :
    f_s_instant wit s u v ≥ 0 := by
  apply Finset.sum_nonneg
  intro r hr
  apply le_of_lt
  apply wit.wt_pos
  -- hr : r ∈ (instantFlow_arc wit u v) ∩ (wit.idx.filter (s.src ∈ ...))
  have h1 := Finset.mem_inter.mp hr
  have h2 := Finset.mem_inter.mp h1.1
  have h3 := (Finset.mem_filter.mp h2.1).1
  exact h3

-- ============================================================================
-- SECTION 3 — KEY LEMMA: LAYER SUM (Partition Lemma P1)
-- ============================================================================
--
-- Chapter 5, lines 1071–1082:
--   ∑_{v ∈ Delta(e.k+1)} f_instant wit e v = (instantFlow_S_O wit e).sum wit.weight
--
-- Proof: S_O(e) = ⊔_{v ∈ Delta(e.k+1)} (S_O(e) ∩ S_O(v))  (disjoint union)
-- by Pedigree.unique_at_layer. Then Finset.sum_biUnion gives the result.
-- Pattern from MCFNecessityProof.lean: pedigree_bipartite_flow_feasible.

/-- Partition Lemma P1: outflow from e = total weight of pedigrees through e.
    Requires hek : e.k ≤ k so that layer e.k+1 ≤ k+1 is within wit.ped range. -/
lemma instantFlow_outflow {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X)
    (e : Triple) (he : e ∈ Delta e.k) (hek : e.k ≤ k) :
    (Delta (e.k + 1)).sum (fun v => f_instant wit e v) =
    (instantFlow_S_O wit e).sum wit.weight := by
  simp only [f_instant, instantFlow_arc]
  have hek3  : 3 ≤ e.k + 1     := by linarith [mem_Delta_l3 he]
  have hek_le : e.k + 1 ≤ k + 1 := by omega
  -- For each r ∈ S_O(e), find the unique v ∈ Delta(e.k+1) in (wit.ped r).triangles
  have get_next : ∀ r ∈ instantFlow_S_O wit e,
      ∃ v ∈ Delta (e.k + 1), v ∈ (wit.ped r).triangles := by
    intro r hr
    obtain ⟨v, ⟨hv_mem, hv_k⟩, _⟩ :=
      Pedigree.unique_at_layer (wit.ped r) (e.k + 1) hek3 hek_le
    -- v ∈ Delta (e.k+1): from h_in_delta + hv_k
    -- Use List.mem_iff_getElem to get index
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hv_mem
    have hdel := (wit.ped r).h_in_delta i hi
    simp only [List.get_eq_getElem] at hdel
    rw [hget, hv_k] at hdel
    exact ⟨v, hdel, hv_mem⟩
  -- Coverage: S_O(e) = ∪_v (S_O(e) ∩ S_O(v))
  have hcover : instantFlow_S_O wit e =
      (Delta (e.k + 1)).biUnion
        (fun v => instantFlow_S_O wit e ∩ instantFlow_S_O wit v) := by
    ext r
    simp only [Finset.mem_biUnion, Finset.mem_inter,
               instantFlow_S_O, Finset.mem_filter]
    constructor
    · intro ⟨hr_idx, hr_e⟩
      obtain ⟨v, hv_delta, hv_mem⟩ :=
        get_next r (Finset.mem_filter.mpr ⟨hr_idx, hr_e⟩)
      -- goal: ∃ v ∈ Delta(e.k+1), (r ∈ idx ∧ e ∈ ped r) ∧ (r ∈ idx ∧ v ∈ ped r)
      exact ⟨v, hv_delta, ⟨hr_idx, hr_e⟩, ⟨hr_idx, hv_mem⟩⟩
    · rintro ⟨_, _, ⟨hr_idx, hr_e⟩, -⟩
      exact ⟨hr_idx, hr_e⟩
  -- Disjointness: S_O(e) ∩ S_O(v₁) and S_O(e) ∩ S_O(v₂) disjoint for v₁ ≠ v₂
  -- Set.PairwiseDisjoint required by Finset.sum_biUnion signature
  -- After intro, goal is Function.onFun Disjoint f v₁ v₂
  -- simp [Function.onFun] unfolds to Disjoint (f v₁) (f v₂)
  -- then Finset.disjoint_left: ∀ r ∈ A, r ∉ B
  have hdisjoint : Set.PairwiseDisjoint
      (↑(Delta (e.k + 1)) : Set Triple)
      (fun v => instantFlow_S_O wit e ∩ instantFlow_S_O wit v) := by
    intro v₁ hv₁ v₂ hv₂ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro r hr₁ hr₂
    -- v₁ and v₂ both in (wit.ped r).triangles at layer e.k+1
    have hv1_mem : v₁ ∈ (wit.ped r).triangles :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hr₁).2).2
    have hv2_mem : v₂ ∈ (wit.ped r).triangles :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hr₂).2).2
    have hv1k : v₁.k = e.k + 1 := mem_Delta_k (Finset.mem_coe.mp hv₁)
    have hv2k : v₂.k = e.k + 1 := mem_Delta_k (Finset.mem_coe.mp hv₂)
    -- unique_at_layer → v₁ = v₂ → contradicts hne
    obtain ⟨_, _, huniq⟩ :=
      Pedigree.unique_at_layer (wit.ped r) (e.k + 1) hek3 hek_le
    -- huniq : ∀ t, t ∈ triangles ∧ t.k = e.k+1 → t = the_unique
    -- List.Mem has multiple constructors → use And.intro explicitly
    have heq : v₁ = v₂ :=
      (huniq v₁ (And.intro hv1_mem hv1k)).trans
      (huniq v₂ (And.intro hv2_mem hv2k)).symm
    exact absurd heq hne
  -- Apply: goal is ∑ v ∈ Delta, (S_O(e) ∩ S_O(v)).sum w = S_O(e).sum w
  -- Step: rewrite LHS using ← sum_biUnion → (biUnion ...).sum w
  -- Then:  rewrite ← hcover → S_O(e).sum w  ✓
  rw [← Finset.sum_biUnion hdisjoint, ← hcover]

-- ============================================================================
-- SECTION 4 — MAIN THEOREM: NECESSITY
-- ============================================================================

/-- Theorem imptheorem  (Chapter 5, Theorem imptheorem, line 1033):
--
--   Given X/k+1 ∈ conv(P_{k+1}) (witnessed by wit : ConvexWitness n (k+1) X),
--   the instant flow construction gives a feasible MCF(k) with z* = z_max.
--
-- The construction:
--   commodities := arcs in F_k  (pairs (e', e) with e' at layer k, e at k+1,
--                                 e' ∈ generators e, wit has positive flow)
--   f_s(s, u, v) := f_s_instant wit s u v
--
-- Verification uses wit.wt_pos, wit.wt_sum, wit.combo directly,
-- without InstantFlow.lean (which uses the old Triple API). -/
theorem necessity
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k)
    (wit : ConvexWitness n (k + 1) X) :
    Nonempty (MCFFeasible n k net X) := by
  -- Build the list of commodities from positive-flow arcs in F_k
  -- Each commodity s corresponds to arc (s.src at layer k, tgt at layer k+1)
  -- with flow_val = ∑_{r ∈ I_s(λ)} λ_r
  refine ⟨{
    -- Build commodities from layer-k nodes with positive instant flow to wit.idx
    -- Each commodity s corresponds to a layer-k node u where
    -- f_instant wit u s.src > 0 for some s.src at layer k+1.
    -- Since we are constructing the necessity witness, the commodities are
    -- the layer-k nodes of net that carry positive flow in the instant flow.
    -- Each such u becomes a Commodity with src = u and flow_val = (instantFlow_S_O wit u).sum wit.weight
    -- [N2] Build commodities from layer-k nodes with positive instant flow.
    -- Each commodity s = { src = u, tgt = v, flow_val = (S_O u).sum weight }
    -- where u ∈ N_k with u.k = k, and v ∈ Delta(k+1) is the unique destination.
    -- tgt, h_src_layer, h_tgt_layer filled once tgt construction is settled.
    commodities := sorry

    f_s         := fun s u v => f_s_instant wit s u v
    f_rigid_s   := fun _P _s _v => 0  -- no rigid flow in necessity construction
    f_s_nn      := fun s u v => f_s_instant_nn wit s u v
    f_rigid_s_nn := fun _P _s _v => le_refl 0

    f_s_valid := by
      intro s u v hpos
      -- f_s_instant wit s u v > 0 means ∃ r ∈ wit.idx with u,v ∈ (wit.ped r).triangles
      -- Since wit.ped r is a valid Pedigree, u.k + 1 = v.k, so
      -- Pedigree.h_generators gives u ∈ generators v.
      -- f_s_instant > 0 → ∃ r with u,v ∈ (wit.ped r).triangles
      -- Since wit.ped r is a valid Pedigree with u.k+1 = v.k,
      -- Pedigree.h_generators gives u ∈ generators v.
      sorry -- [N1] from Pedigree.h_generators applied to u,v ∈ (wit.ped r).triangles

    f_s_node := by
      intro s u v hpos
      -- f_s_instant > 0 → ∃ r with f_s r u v > 0 → u ∈ net.nodes from wit structure
      -- The ConvexWitness pedigrees live within the layered network
      sorry -- [N1] u ∈ net.nodes from wit.ped validity

    triangles_valid := by
      intro P hP t ht
      -- P ∈ net.rigid and t ∈ P.triangles → t ∈ Delta t.k
      -- From RigidEntry structure: triangles : Finset Triple
      -- We need t ∈ Delta t.k — this holds by definition of valid triples
      sorry -- [N1] from RigidEntry triangles validity

    conservation := by
      intro s hs u hu hlt
      -- Probability partition at node u:
      -- inflow  = Σ_{w: w.k+1=u.k} f_s_instant wit s w u
      --         = (S_O(s.src) ∩ S_O(u)).sum weight  [instantFlow_outflow at u.k-1]
      -- outflow = Σ_{w: u.k+1=w.k} f_s_instant wit s u w
      --         = (S_O(s.src) ∩ S_O(u)).sum weight  [instantFlow_outflow at u.k]
      -- Both equal by probability partition (unique triangle per layer)
      sorry -- [N1] instantFlow_outflow applied at u.k and u.k-1

    layer_sum := by
      intro s hs l hl hlk
      -- ∑_{t ∈ Delta l} f_s_instant wit s t (s.src)
      -- = (S_O(s.src)).sum weight  [unique_at_layer at l]
      -- = s.flow_val               [definition of commodity]
      sorry -- [N1] unique_at_layer + flow_val definition

    flow_le_slack := by
      intro s hs q hq hqk t ht
      sorry -- [N1] Chapter 5, lines 1164–1167

    slack_nonneg := by
      intro s hs q hq hqk t ht
      sorry -- [N1] slack non-negativity

    flow_vals := by
      intro s hs
      -- s.flow_val = (S_O(s.src) ∩ S_O(s.arc_head)).sum weight  [def of commodity]
      -- = Σ_v f_s_instant wit s s.src v                          [instantFlow_outflow at s.src]
      -- since s.arc_head is the unique successor of s.src at layer k+1
      sorry -- [N2] instantFlow_outflow at s.src + uniqueness of s.arc_head

    total_flow := by
      -- Goal: commodities.foldl (fun acc s => acc + s.flow_val) 0 = zMax net
      -- Key: wit.idx = I_commodity ⊔ I_rigid (disjoint partition)
      --   Σ_s v^s = I_commodity.sum weight
      --   rigid_foldl = I_rigid.sum weight  [each P ∈ R_k has weight = Σ_{r ∈ 𝕊_P} λ_r]
      --   Σ_s v^s + rigid_foldl = wit.wt_sum = 1
      --   zMax net = 1 - rigid_foldl  [from net.z_max_eq]
      --   Hence Σ_s v^s = zMax net
      sorry -- [N3] partition wit.idx + wit.wt_sum + net.z_max_eq

    hk := by sorry  -- [N4] needs 5 ≤ k; necessity has 4 ≤ k — strengthen to hk : 5 ≤ k

    -- X/k ∈ conv(P_k): truncate each pedigree in wit from k+1 to k
    conv_wit    := {
      idx    := wit.idx
      ped    := fun r => (wit.ped r).truncate k ⟨by
        have := (wit.ped r).h_n; omega, by
        have := (wit.ped r).h_length; omega⟩
      weight := wit.weight
      wt_pos := wit.wt_pos
      wt_sum := wit.wt_sum
      combo  := by
        intro t ht
        have hcombo := wit.combo t (by omega)
        rw [← hcombo]
        apply Finset.sum_congr rfl; intro r _
        congr 1
        -- t ∈ List.take (k-2) (wit.ped r).triangles ↔ t ∈ (wit.ped r).triangles
        have hmem_iff : t ∈ ((wit.ped r).truncate k ⟨by have := (wit.ped r).h_n; omega,
            by have := (wit.ped r).h_length; omega⟩).triangles ↔
            t ∈ (wit.ped r).triangles := by
          simp only [Pedigree.truncate]
          constructor
          · exact List.mem_of_mem_take
          · intro hmem
            obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
            have hlay := (wit.ped r).h_layers i hi
            have hlen := (wit.ped r).h_length
            have hn   := (wit.ped r).h_n
            simp only [List.get_eq_getElem, Triple.k] at hlay
            have hi_bound : i < k - 2 := by
              have htk_t : t.k = i + 3 := by
                have heq : ((wit.ped r).triangles.get ⟨i, hi⟩).k = i + 3 := by
                  simp only [List.get_eq_getElem]; exact hlay
                simp only [Triple.k] at ht ⊢; rw [← hget]; exact_mod_cast heq
              simp only [Triple.k] at ht htk_t; omega
            rw [List.mem_iff_getElem]
            refine ⟨i, ?_, ?_⟩
            · simp only [List.length_take]
              apply Nat.lt_min.mpr
              constructor
              · omega
              · exact hi
            · simp only [List.getElem_take]
              exact hget
        simp only [if_congr hmem_iff rfl rfl]}

    X_layer_sum := by
      intro l hl hle
      -- For l = k+1: from wit.combo + wit.wt_sum
      -- For l ≤ k: from conv_wit (sorry'd via truncation)
      sorry -- [N4] layer sum from ConvexWitness

    X_nn := by
      intro t
      -- X t = Σ_r λ_r * indicator(t ∈ ped r) ≥ 0
      -- since λ_r > 0 and indicator ∈ {0,1}
      by_cases htk : t.k ≤ k + 1
      · have hcombo := wit.combo t htk
        rw [← hcombo]
        apply Finset.sum_nonneg; intro r hr
        exact mul_nonneg (le_of_lt (wit.wt_pos r hr))
          (by split_ifs <;> norm_num)
      · -- t outside range: X t = 0 ≥ 0
        sorry -- [N4] X t = 0 outside Delta range

    pos_X_node := by
      sorry -- [N4] X t > 0 → t ∈ net.nodes

    src_node_val := by
      sorry -- [N4] X s.src = 1 for each commodity s

    f_s_target := by
      sorry -- [N4] f_s s u v > 0 → v ∈ net.nodes

    f_rigid_s_target := by
      intro _P _s _v hpos
      -- f_rigid_s = 0 everywhere in necessity construction
      simp at hpos

    src_in_net := by
      sorry -- [N4] s.src ∈ net.nodes

    head_in_net := by
      sorry -- [N4] s.arc_head ∈ net.nodes

    ext_new := by
      sorry -- [N4] arc_head is new

    src_val := by
      sorry -- [N4] X s.arc_head = 1

    source_flow := by
      sorry -- [N4] flow from (1,2,3) = s.flow_val

    col_sum_le := by
      sorry -- [N4] column sum ≤ s.flow_val

    rigid_combo := by
      sorry -- [N4] X t from rigid pedigrees when N_k = ∅
  }⟩

end MembershipProject.Core
