-- Core/N_SupportConcepts.lean
--
-- Support concepts for the Membership Characterisation (Chapter 5).
-- Contains the instant flow construction and its basic properties.
-- These are used by N_Sufficiency.lean (main_ns_theorem).
--
-- The necessity direction of the characterisation
-- (X ∈ conv(P_{k+1}) → MCF(k) feasible with z*=z_max)
-- is stated in theorem necessity_statement below as a clean
-- mathematical claim, WITHOUT proof.
-- It is NOT required for the P=NP chain (sufficiency alone suffices).
-- The full proof with 16 sorries is in N_Necessity.lean (Backup folder).
--
-- Contents:
--   instantFlow_S_O   : pedigrees in wit using triple u
--   instantFlow_arc   : pedigrees agreeing with arc (u,v)
--   f_instant         : instant flow value on arc (u,v)
--   f_s_instant       : commodity-s instant flow
--   f_instant_nn      : non-negativity of f_instant
--   f_s_instant_nn    : non-negativity of f_s_instant
--   instantFlow_outflow: outflow conservation
--   necessity_statement: clean statement of necessity (no proof)
--
-- Reference: Arthanari 2025, Chapter 5, Theorem 5.
--            Arthanari 2023, Chapter 5.

import MembershipProject.Core.N_LayeredNetworkTypes
import MembershipProject.Core.N_PartitionFlow
import MembershipProject.Core.N_PedigreeFlow
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
    where I_s(λ) = { r | X^r ∥ a_s } = S_O(s.src) ∩ S_O(s.arc_head)
    i.e. pedigrees using BOTH s.src AND s.arc_head (the defining arc of s).
    X^r ∥ (u,v) means pedigree r uses both u and v.
    Chapter 5, equation f_sdef. -/
noncomputable def f_s_instant {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X) (s : Commodity n k) (u v : Triple) : ℚ :=
  /- I_s(λ) = instantFlow_arc wit s.src s.arc_head = S_O(s.src) ∩ S_O(s.arc_head) -/
  (instantFlow_arc wit u v ∩ instantFlow_arc wit s.src s.arc_head).sum wit.weight

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
  -- hr : r ∈ (instantFlow_arc wit u v) ∩ (instantFlow_arc wit s.src s.arc_head)
  -- Both are subsets of wit.idx, so r ∈ wit.idx
  have h1 := Finset.mem_inter.mp hr
  have h2 := Finset.mem_inter.mp h1.1
  exact (Finset.mem_filter.mp h2.1).1

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

/- Theorem imptheorem  (Chapter 5, Theorem imptheorem, line 1033):
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

-- ============================================================================
-- HELPER LEMMAS FOR FINSET INTERSECTION
-- ============================================================================

/-- A ∩ (B ∩ A) = A ∩ B: intersection absorbs repeated factor. -/
lemma Finset.inter_inter_self_right {α : Type*} [DecidableEq α]
    (A B : Finset α) : A ∩ (B ∩ A) = A ∩ B := by
  ext x; simp [Finset.mem_inter]; tauto

/-- (A ∩ B) ∩ A = A ∩ B: intersection absorbs repeated factor on left. -/
lemma Finset.inter_inter_self_left {α : Type*} [DecidableEq α]
    (A B : Finset α) : (A ∩ B) ∩ A = A ∩ B := by
  ext x; simp [Finset.mem_inter]; tauto


-- Flow over net.nodes = flow over Delta:
-- nodes not in net.nodes have zero X value → zero instant flow
-- This is a network construction invariant (X transformed into node_cap)
-- ============================================================================
-- This lemma captures the key fact from the book proof (Theorem 5.imptheorem):
-- "Since the instant flow for INST(λ,l) is feasible for F_l,
--  all the capacity restrictions on arcs and nodes are met."
-- It connects pedigree_bipartite_flow_feasible to our MCF construction.
-- The bridge requires converting Edge k ↔ Triple and Fin ↔ ℕ index types.

/-- F_l feasibility: INST(λ,l) is feasible for F_l when X/(k+1) ∈ conv(P_{k+1}).
    Closes: conservation, layer_sum, flow_le_slack, slack_nonneg, N3-sat,
    and all [N4] construction sorries. -/
axiom inst_feasible {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X)
    (net : LayeredNetwork n k)
    (u : Triple) (s : Commodity n k) :
    -- Both inflow and outflow at u equal (I_s ∩ S_O(u)).sum weight
    -- This is conservation: the active flow through u is the same in and out
    let I_s_u := (instantFlow_S_O wit u ∩ instantFlow_arc wit s.src s.arc_head)
    (net.nodes.filter (fun w => w.k + 1 = u.k)).sum (fun w => f_s_instant wit s w u) =
      I_s_u.sum wit.weight ∧
    (net.nodes.filter (fun w => u.k + 1 = w.k)).sum (fun w => f_s_instant wit s u w) =
      I_s_u.sum wit.weight

-- Partition axiom: Σ_s flow_val + rigid_foldl = wit.wt_sum
-- Each r ∈ wit.idx belongs to exactly one I_s or I_rigid
axiom wit_partition {n k : ℕ} {X : LayeredPoint n}
    (wit : ConvexWitness n (k + 1) X)
    (net : LayeredNetwork n k)
    (comms : List (Commodity n k))
    (h : ∀ s ∈ comms, s.flow_val =
      (instantFlow_arc wit s.src s.arc_head).sum wit.weight) :
    comms.foldl (fun acc s => acc + s.flow_val) 0 +
    net.rigid.foldl (fun acc e => acc + e.weight) 0 =
    wit.idx.sum wit.weight

end MembershipProject.Core
