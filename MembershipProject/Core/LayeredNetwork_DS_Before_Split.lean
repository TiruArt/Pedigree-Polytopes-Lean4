-- Core/LayeredNetwork.lean
--
-- Formalisation of the Layered Network Framework for M3P
--

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import MembershipProject.Core.Basic
import MembershipProject.Core.Types
import MembershipProject.Core.RestrictionFull
import MembershipProject.Core.MatrixOps
import MembershipProject.Core.SlackComputation
import MembershipProject.Core.PedigreeMembershipCharacterisation
import MembershipProject.Core.PedigreeDefinition
import MembershipProject.Core.MIRFeasible
import MembershipProject.Core.PartitionProbabilityFlowProblem
import MembershipProject.Core.MCFNecessityProof

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace MembershipProject.Core

open Nat
open Finset
open BigOperators

-- ============================================================================
-- SECTION 1: BUILDING BLOCKS
-- ============================================================================

/-- A node v = [k : e] in the layered network. -/
structure LNode where
  triple   : Triple
  cap      : ℚ
  cap_nn   : cap ≥ 0
  deriving Repr

/-- A rigid pedigree P ∈ R_l with weight μ_P. -/
structure RigidEntry (n : ℕ) where
  pedigree : Pedigree n
  weight   : ℚ
  wt_pos   : weight > 0

/-- The point X being tested, restricted to a layer range. -/
structure LayeredPoint (n : ℕ) where
  x      : Triple → ℚ
  x_nn   : ∀ t, x t ≥ 0
  x_le1  : ∀ t, x t ≤ 1
  sum_eq : ∀ k, 3 ≤ k → k ≤ n →
    (Delta k).sum (fun t => x t) = 1

-- ============================================================================
-- SECTION 2: THE LAYERED NETWORK
-- ============================================================================

/-- The layered network at stage k. -/
structure LayeredNetwork (n k : ℕ) where
  nodes     : Finset Triple
  node_cap  : Triple → ℚ
  cap_nn    : ∀ v ∈ nodes, node_cap v ≥ 0
  node_layers : ∀ v ∈ nodes, 4 ≤ v.k ∧ v.k ≤ k
  arc_valid : ∀ u v : Triple, u ∈ nodes → v ∈ nodes →
    u.k + 1 = v.k → u ∈ generators v
  rigid     : List (RigidEntry n)
  well_def  : nodes.Nonempty ∨ rigid ≠ []
  z_max_eq  : (nodes.filter (fun v => v.k = k)).sum node_cap +
              (rigid.map (fun e => e.weight)).sum = 1

/-- z_max: the maximum achievable flow in MCF(k). -/
noncomputable def zMax {n k : ℕ} (net : LayeredNetwork n k) : ℚ :=
  1 - (net.rigid.map (fun e => e.weight)).sum

lemma zMax_eq_node_caps {n k : ℕ} (net : LayeredNetwork n k) :
    zMax net = (net.nodes.filter (fun v => v.k = k)).sum net.node_cap := by
  unfold zMax
  linarith [net.z_max_eq]

-- ============================================================================
-- SECTION 3: THE FAT PROBLEM F_k
-- ============================================================================

/-- Check if u generates v -/
def isGenerator (u v : Triple) : Prop :=
  u ∈ generators v

/-- Feasibility of F_k. -/
structure FATkFeasible (n k : ℕ) (net : LayeredNetwork n k) (X : LayeredPoint n) where
  f_node   : Triple → Triple → ℚ
  f_rigid  : RigidEntry n → Triple → ℚ
  f_node_nn  : ∀ u v, f_node u v ≥ 0
  f_rigid_nn : ∀ P v, f_rigid P v ≥ 0
  f_node_valid : ∀ u v, f_node u v > 0 →
    u.k = k → v.k = k + 1 → isGenerator u v
  supply_node : ∀ u ∈ net.nodes, u.k = k →
    (Delta (k + 1)).sum (fun v => f_node u v) ≤ net.node_cap u
  supply_rigid : ∀ P ∈ net.rigid,
    (Delta (k + 1)).sum (fun v => f_rigid P v) ≤ P.weight
  demand : ∀ v : Triple, v.k = k + 1 → X.x v > 0 →
    (net.nodes.filter (fun u => u.k = k)).sum (fun u => f_node u v) +
    (net.rigid.map (fun P => f_rigid P v)).sum = X.x v
  total : (Delta (k + 1)).sum (fun v =>
    (net.nodes.filter (fun u => u.k = k)).sum (fun u => f_node u v) +
    (net.rigid.map (fun P => f_rigid P v)).sum) = zMax net

-- ============================================================================
-- SECTION 4: COMMODITY STRUCTURE
-- ============================================================================

/-- A single commodity s in the multicommodity flow problem. -/
structure Commodity (n k : ℕ) where
  src  : Triple
  tgt  : Triple
  h_src_layer : src.k = k
  h_tgt_layer : tgt.k = k + 1
  h_arc_valid : isGenerator src tgt
  flow_val : ℚ
  flow_pos : flow_val > 0

/-- Y^s vector for commodity s. -/
noncomputable def commodityVector {n k : ℕ}
    (s : Commodity n k)
    (f_s : Triple → Triple → ℚ)
    (net : LayeredNetwork n k) : Triple → ℚ :=
  fun u =>
    (Delta (k + 1)).sum (fun v => f_s u v) +
    (net.rigid.map (fun P =>
      if u ∈ P.pedigree.triangles then
        s.flow_val
      else 0)).sum

-- ============================================================================
-- SECTION 5: THE MCF PROBLEM MCF(k)
-- ============================================================================

/-- A feasible solution to MCF(k) with value z_max. -/
structure MCFFeasible (n k : ℕ) (net : LayeredNetwork n k) (X : LayeredPoint n) where
  commodities : List (Commodity n k)
  f_s : Commodity n k → Triple → Triple → ℚ
  f_s_nn  : ∀ s u v, f_s s u v ≥ 0
  f_s_valid : ∀ s u v, f_s s u v > 0 → isGenerator u v
  conservation : ∀ s ∈ commodities, ∀ u ∈ net.nodes, u.k < k →
    (net.nodes.filter (fun w => w.k + 1 = u.k)).sum (fun w => f_s s w u) =
    (net.nodes.filter (fun w => u.k + 1 = w.k)).sum (fun w => f_s s u w)
  node_cap : ∀ v ∈ net.nodes,
    (commodities.map (fun s =>
      (net.nodes.filter (fun u => u.k + 1 = v.k)).sum (fun u => f_s s u v))).sum ≤
    net.node_cap v
  flow_vals : ∀ s ∈ commodities, s.flow_val =
    (Delta (k + 1)).sum (fun v => f_s s s.src v)
  total_flow : (commodities.map (fun s => s.flow_val)).sum = zMax net

-- ============================================================================
-- SECTION 6: CONVEX WITNESS
-- ============================================================================

/-- A convex witness: λ ∈ Λ_{k+1}(X). -/
structure ConvexWitness (n k : ℕ) (X : LayeredPoint n) where
  idx    : Finset ℕ
  ped    : ℕ → Pedigree k
  weight : ℕ → ℚ
  wt_pos : ∀ r ∈ idx, weight r > 0
  wt_sum : idx.sum weight = 1
  combo  : ∀ t : Triple, t.k ≤ k →
    idx.sum (fun r => weight r *
      if t ∈ (ped r).triangles then 1 else 0) = X.x t

/-- Helper to cast a convex witness to a different k (by equality). -/
def ConvexWitness.cast {n k₁ k₂ : ℕ} {X : LayeredPoint n} (h : k₁ = k₂)
    (wit : ConvexWitness n k₁ X) : ConvexWitness n k₂ X :=
  { idx := wit.idx
    ped := fun i => by
      have : k₁ = k₂ := h
      exact h ▸ wit.ped i
    weight := wit.weight
    wt_pos := wit.wt_pos
    wt_sum := wit.wt_sum
    combo := fun t ht => by
      subst h
      exact wit.combo t ht }

-- ============================================================================
-- SECTION 7: NECESSITY DIRECTION
-- ============================================================================

-- First, let's create a simple wrapper to avoid Fintype ℕ issues
def natFintype : Fintype ℕ := inferInstance

/-- Necessity: X/(k+1) ∈ conv(P_{k+1}) implies MCF(k) achieves z_max. -/
theorem necessity
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X    : LayeredPoint n)
    (net  : LayeredNetwork n k)
    (wit  : ConvexWitness n (k + 1) X) :
    Nonempty (MCFFeasible n k net X) := by

  -- Domain = set of active pedigree indices
  let D := wit.idx

  -- Convert to PedigreeStructure (following MCFNecessityProof.lean pattern)
  -- We need to provide explicit instances
  have : DecidableEq ℕ := by infer_instance
  have : Fintype ℕ := by infer_instance

  let ped : @PedigreeStructure ℕ n _ _ :=
    { pedigrees := D
      weights := fun r => if r ∈ D then (wit.weight r : ℝ) else 0
      h_nonneg := by
        intro r hr
        simp only [hr, ite_true]
        exact (Rat.cast_nonneg.2 (le_of_lt (wit.wt_pos r hr)))
      h_sum_one := by
        simp only [Finset.sum_ite_mem, Finset.sum_const_zero, add_zero]
        have h_sum : ∑ r in D, (wit.weight r : ℝ) = 1 := by
          rw [← Rat.cast_sum, wit.wt_sum]
          norm_cast
        exact h_sum
      h_support := by
        intro r hr
        simp only [hr, ite_false]
    }

  -- Origins at layer k
  let edges_k := net.nodes.filter fun u => u.k = k
  let S_O (e : Triple) : Finset ℕ := D.filter fun r => e ∈ (wit.ped r).triangles

  -- Destinations at layer k+1
  let edges_k1 := (Delta (k + 1)).filter fun v => X.x v > 0
  let S_D (v : Triple) : Finset ℕ := D.filter fun r => v ∈ (wit.ped r).triangles

  -- ======================================================================
  -- PART 1: Show that (edges_k, S_O) forms a partition of D
  -- ======================================================================

  have h_O_partition : (∀ e ∈ edges_k, (S_O e).Nonempty) ∧
      (∀ e₁ e₂ ∈ edges_k, e₁ ≠ e₂ → Disjoint (S_O e₁) (S_O e₂)) ∧
      (Finset.biUnion edges_k S_O) = D := by
    constructor
    · -- Part 1a: Nonemptiness
      intro e he
      have h_node : e ∈ net.nodes := (mem_filter.mp he).1
      have h_cap_pos : net.node_cap e > 0 := by
        -- Nodes in the network have positive capacity (by construction)
        -- This follows from network well-formedness
        sorry
      have h_xe_eq : X.x e = net.node_cap e := by
        -- node_cap is the updated capacity x̄(e) = X.x e (non-rigid)
        -- This is a property of layered networks
        sorry
      have h_xe_pos : X.x e > 0 := by rw [h_xe_eq]; exact h_cap_pos

      -- Sum over S_O(e) equals X.x e by convex witness
      have h_sum_eq : ∑ r in S_O e, (wit.weight r : ℝ) = X.x e := by
        have := wit.combo e (by simp [he])
        simp only [S_O] at this
        have h_sum_rat : ∑ r in S_O e, wit.weight r = X.x e := by
          rw [← Finset.sum_filter] at this
          exact this
        rw [← Rat.cast_sum] at h_sum_rat
        exact h_sum_rat

      exact Finset.nonempty_of_sum_ne_zero (by linarith [h_xe_pos, h_sum_eq])

    · constructor
      · -- Part 1b: Disjointness
        intro e₁ he₁ e₂ he₂ hne
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext r
        simp [S_O, Finset.mem_inter]
        intro ⟨h1, h2⟩
        -- Each pedigree has exactly one triangle at layer k
        have h_stages := (wit.ped r).h_stages k (by omega) (by omega)
        obtain ⟨t, ⟨ht, _⟩, huniq⟩ := h_stages
        have h_eq₁ : t = e₁ := huniq e₁ ⟨h1, by simp [e₁]⟩
        have h_eq₂ : t = e₂ := huniq e₂ ⟨h2, by simp [e₂]⟩
        rw [h_eq₁, h_eq₂] at hne
        contradiction

      · -- Part 1c: Coverage
        ext r
        simp [Finset.mem_biUnion, S_O]
        constructor
        · -- Forward: r ∈ D → ∃ e ∈ edges_k with e ∈ (ped r).triangles
          intro hr
          have h_stages := (wit.ped r).h_stages k (by omega) (by omega)
          obtain ⟨e, ⟨he, _⟩, _⟩ := h_stages
          -- Show e ∈ edges_k (i.e., X.x e > 0)
          have h_xe_pos : X.x e > 0 := by
            have := wit.combo e (by simp)
            simp [S_O] at this
            have h_sum_rat : ∑ r' in S_O e, wit.weight r ≥ wit.weight r :=
              Finset.single_le_sum (fun r' hr' => (wit.wt_pos r' hr').le) (by simp [he])
            have h_eq : X.x e = ∑ r' in S_O e, wit.weight r := by
              have := wit.combo e (by simp)
              simp [S_O] at this
              exact this
            linarith [h_sum_rat, wit.wt_pos r hr, h_eq]
          have h_e_in : e ∈ edges_k := by
            simp [edges_k]
            -- Need lemma: if X.x e > 0 then e ∈ net.nodes
            have h_node : e ∈ net.nodes := by
              -- This follows from the network definition
              sorry
            exact ⟨h_node, by simp [e]⟩
          exact ⟨e, h_e_in, he⟩

        · -- Reverse: if e ∈ edges_k and e ∈ (ped r).triangles, then r ∈ D
          intro ⟨e, he, hmem⟩
          exact (mem_filter.mp hmem).1

  -- ======================================================================
  -- PART 2: Show that (edges_k1, S_D) forms a partition of D
  -- ======================================================================
  have h_D_partition : (∀ v ∈ edges_k1, (S_D v).Nonempty) ∧
      (∀ v₁ v₂ ∈ edges_k1, v₁ ≠ v₂ → Disjoint (S_D v₁) (S_D v₂)) ∧
      (Finset.biUnion edges_k1 S_D) = D := by
    -- Symmetric to h_O_partition using wit.combo for layer k+1
    constructor
    · -- Part 2a: Nonemptiness
      intro v hv
      have h_v_in_Delta : v ∈ Delta (k + 1) := (mem_filter.mp hv).1
      have h_xv_pos : X.x v > 0 := (mem_filter.mp hv).2

      -- Sum over S_D(v) equals X.x v by convex witness
      have h_sum_eq : ∑ r in S_D v, (wit.weight r : ℝ) = X.x v := by
        have := wit.combo v (by simp [hv])
        simp only [S_D] at this
        have h_sum_rat : ∑ r in S_D v, wit.weight r = X.x v := by
          rw [← Finset.sum_filter] at this
          exact this
        rw [← Rat.cast_sum] at h_sum_rat
        exact h_sum_rat

      exact Finset.nonempty_of_sum_ne_zero (by linarith [h_xv_pos, h_sum_eq])

    · constructor
      · -- Part 2b: Disjointness
        intro v₁ hv₁ v₂ hv₂ hne
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext r
        simp [S_D, Finset.mem_inter]
        intro ⟨h1, h2⟩
        -- Each pedigree has exactly one triangle at layer k+1
        have h_stages := (wit.ped r).h_stages (k + 1) (by omega) (by omega)
        obtain ⟨t, ⟨ht, _⟩, huniq⟩ := h_stages
        have h_eq₁ : t = v₁ := huniq v₁ ⟨h1, by simp [v₁]⟩
        have h_eq₂ : t = v₂ := huniq v₂ ⟨h2, by simp [v₂]⟩
        rw [h_eq₁, h_eq₂] at hne
        contradiction

      · -- Part 2c: Coverage
        ext r
        simp [Finset.mem_biUnion, S_D]
        constructor
        · -- Forward: r ∈ D → ∃ v ∈ edges_k1 with v ∈ (ped r).triangles
          intro hr
          have h_stages := (wit.ped r).h_stages (k + 1) (by omega) (by omega)
          obtain ⟨v, ⟨hv, _⟩, _⟩ := h_stages
          -- Show v ∈ edges_k1 (i.e., X.x v > 0)
          have h_xv_pos : X.x v > 0 := by
            have := wit.combo v (by simp)
            simp [S_D] at this
            have h_sum_rat : ∑ r' in S_D v, wit.weight r ≥ wit.weight r :=
              Finset.single_le_sum (fun r' hr' => (wit.wt_pos r' hr').le) (by simp [hv])
            have h_eq : X.x v = ∑ r' in S_D v, wit.weight r := by
              have := wit.combo v (by simp)
              simp [S_D] at this
              exact this
            linarith [h_sum_rat, wit.wt_pos r hr, h_eq]
          have h_v_in : v ∈ edges_k1 := by
            simp [edges_k1]
            exact ⟨hv, h_xv_pos⟩
          exact ⟨v, h_v_in, hv⟩

        · -- Reverse: if v ∈ edges_k1 and v ∈ (ped r).triangles, then r ∈ D
          intro ⟨v, hv, hmem⟩
          exact (mem_filter.mp hmem).1

  -- ======================================================================
  -- PART 3: Build LayerStructure following MCFNecessityProof.lean pattern
  -- ======================================================================

  let layer : @LayerStructure ℕ n k ped _ _ :=
    { edges_k := edges_k
      edges_k1 := edges_k1
      S_O := S_O
      S_D := S_D
      h_S_O_nonempty := h_O_partition.1
      h_S_O_disjoint := h_O_partition.2.1
      h_S_O_covers := by
        intro r hr
        have := h_O_partition.2.2
        rw [← Finset.mem_biUnion] at this
        exact this r hr
      h_S_O_subsets := by
        intro e he
        simp [S_O]
        exact fun r hr => hr.1
      h_S_D_nonempty := h_D_partition.1
      h_S_D_disjoint := h_D_partition.2.1
      h_S_D_covers := by
        intro r hr
        have := h_D_partition.2.2
        rw [← Finset.mem_biUnion] at this
        exact this r hr
      h_S_D_subsets := by
        intro v hv
        simp [S_D]
        exact fun r hr => hr.1
    }

  -- ======================================================================
  -- PART 4: Apply the pedigree_bipartite_flow_feasible theorem
  -- ======================================================================

  have h_flow := pedigree_bipartite_flow_feasible ped layer

  -- Extract the four flow properties
  have h_origin : ∀ e ∈ edges_k,
      ∑ e' ∈ edges_k1, pedigree_flow ped layer e e' = supply ped layer e :=
    h_flow.1

  have h_sink : ∀ e' ∈ edges_k1,
      ∑ e ∈ edges_k, pedigree_flow ped layer e e' = demand ped layer e' :=
    h_flow.2.1

  have h_nonneg : ∀ e ∈ edges_k, ∀ e' ∈ edges_k1,
      0 ≤ pedigree_flow ped layer e e' :=
    h_flow.2.2.1

  have h_arc : ∀ e ∈ edges_k, ∀ e' ∈ edges_k1,
      S_O e ∩ S_D e' = ∅ → pedigree_flow ped layer e e' = 0 :=
    h_flow.2.2.2

  -- ======================================================================
  -- PART 5: Build commodities list from positive flows
  -- ======================================================================

  let commodities : List (Commodity n k) :=
    (edges_k ×ˢ edges_k1).toList.filterMap (fun (e, v) =>
      let f_val := pedigree_flow ped layer e v
      if h_pos : f_val > 0 then
        some {
          src := e
          tgt := v
          h_src_layer := by simp [(mem_filter.mp e.2).2]
          h_tgt_layer := by simp [(mem_filter.mp v.2).2]
          h_arc_valid := by
            have h_nonempty : (S_O e ∩ S_D v).Nonempty := by
              contrapose! h_pos
              rw [Finset.not_nonempty_iff_eq_empty] at h_pos
              have h_zero := h_arc e e.2 v v.2 h_pos
              rw [h_zero] at h_pos
              simp at h_pos
              exact h_pos
            -- If intersection nonempty, then e generates v
            obtain ⟨r, hr⟩ := h_nonempty
            have h_u : e ∈ (wit.ped r).triangles := (mem_filter.mp hr).2
            have h_v : v ∈ (wit.ped r).triangles := by
              simp [S_D] at hr
              exact hr.2
            exact (wit.ped r).generator_condition e v h_u h_v
          flow_val := f_val
          flow_pos := h_pos
        }
      else none)

  -- ======================================================================
  -- PART 6: Define commodity flows
  -- ======================================================================

  let f_s (s : Commodity n k) (u v : Triple) : ℚ :=
    if u = s.src ∧ v = s.tgt then s.flow_val else 0

  -- ======================================================================
  -- PART 7: Connect pedigree_flow to supply/demand
  -- ======================================================================

  have h_supply_eq : ∀ e ∈ edges_k, supply ped layer e = net.node_cap e := by
    intro e he
    unfold supply
    simp [ped]
    have h_sum : ∑ r in S_O e, (wit.weight r : ℝ) = X.x e := by
      have := wit.combo e (by simp [he])
      simp [S_O] at this
      rw [← Finset.sum_filter] at this
      rw [← Rat.cast_sum]
      exact mod_cast this
    -- Need: X.x e = net.node_cap e
    sorry

  have h_demand_eq : ∀ v ∈ edges_k1, demand ped layer v = X.x v := by
    intro v hv
    unfold demand
    simp [ped]
    have h_sum : ∑ r in S_D v, (wit.weight r : ℝ) = X.x v := by
      have := wit.combo v (by simp [hv])
      simp [S_D] at this
      rw [← Finset.sum_filter] at this
      rw [← Rat.cast_sum]
      exact mod_cast this
    exact h_sum

  -- ======================================================================
  -- PART 8: Construct MCFFeasible
  -- ======================================================================

  exact ⟨{
    commodities := commodities
    f_s := f_s
    f_s_nn := by
      intro s u v
      simp [f_s]
      split_ifs
      · exact s.flow_pos.le
      · rfl
    f_s_valid := by
      intro s u v hpos
      simp [f_s] at hpos
      split_ifs at hpos
      · have h_eq : u = s.src ∧ v = s.tgt := h
        rw [h_eq.1, h_eq.2]
        exact s.h_arc_valid
      · contradiction
    conservation := by
      intro s hs u hu hlt
      simp [f_s]
      by_cases h : u = s.src
      · -- u is source: outflow = flow_val, inflow = 0
        subst h
        have h_out : ∑ w ∈ net.nodes.filter fun w => u.k + 1 = w.k, f_s s u w = s.flow_val := by
          simp [f_s]
          rw [Finset.sum_eq_single_of_mem s.tgt]
          · simp [s.h_tgt_layer]
          · simp [s.h_tgt_layer]
            exact Finset.mem_filter_of_mem (by simp) (by simp [s.h_tgt_layer])
          · intro b hb hneq
            simp [hneq]
        have h_in : ∑ w ∈ net.nodes.filter fun w => w.k + 1 = u.k, f_s s w u = 0 := by
          apply Finset.sum_eq_zero
          intro w hw
          simp
          split_ifs
          · contradiction
          · rfl
        rw [h_out, h_in]
      · -- u is not source: both inflow and outflow are 0
        have h_out : ∑ w ∈ net.nodes.filter fun w => u.k + 1 = w.k, f_s s u w = 0 := by
          apply Finset.sum_eq_zero
          intro w hw
          simp [f_s, h]
        have h_in : ∑ w ∈ net.nodes.filter fun w => w.k + 1 = u.k, f_s s w u = 0 := by
          apply Finset.sum_eq_zero
          intro w hw
          simp [f_s]
          split_ifs
          · contradiction
          · rfl
        rw [h_out, h_in]
    node_cap := by
      intro v hv
      simp
      -- Each commodity contributes only to its source node's capacity
      rw [← zMax_eq_node_caps net]
      sorry
    flow_vals := by
      intro s hs
      simp [f_s]
      rw [Finset.sum_eq_single_of_mem s.tgt]
      · simp
      · simp [s.h_tgt_layer]
        exact Finset.mem_filter_of_mem (by simp) (by simp [s.h_tgt_layer])
      · intro b hb hneq
        simp [hneq]
    total_flow := by
      simp
      -- Sum of flow_vals over commodities equals zMax
      have h_total : ∑ s ∈ commodities, s.flow_val = zMax net := by
        -- Use the origin conservation property
        calc
          ∑ s ∈ commodities, s.flow_val
            = ∑ e ∈ edges_k, ∑ e' ∈ edges_k1, pedigree_flow ped layer e e' := by
                -- Each commodity corresponds to a positive flow arc
                sorry
          _ = ∑ e ∈ edges_k, supply ped layer e := by
                rw [← Finset.sum_congr rfl (fun e he => h_origin e he)]
          _ = ∑ e ∈ edges_k, net.node_cap e := by
                rw [Finset.sum_congr rfl h_supply_eq]
          _ = zMax net := by
                rw [zMax_eq_node_caps net]
      exact h_total
  }, trivial⟩

-- ============================================================================
-- SECTION 8: LEMMAS FOR SUFFICIENCY
-- ============================================================================

/-- Lemma YsinMI (paper §6.2): -/
lemma Y_s_in_PMI
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k)
    (mcf : MCFFeasible n k net X)
    (s   : Commodity n k)
    (hs  : s ∈ mcf.commodities) :
    ∃ F : MIRFeasible k, ∀ e : ℕ × ℕ, F.u 0 e ≤ 1 := by
  sorry

/-- Lemma Ysinconv (paper §6.2): -/
lemma Y_s_in_conv
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k)
    (mcf : MCFFeasible n k net X)
    (s   : Commodity n k)
    (hs  : s ∈ mcf.commodities) :
    ∃ wit : ConvexWitness n k X,
      ∀ r ∈ wit.idx, (wit.ped r).triangles.getLast? = some s.src := by
  sorry

-- ============================================================================
-- SECTION 9: SUFFICIENCY DIRECTION
-- ============================================================================

/-- Sufficiency: MCF(k) achieves z_max implies X/(k+1) ∈ conv(P_{k+1}). -/
theorem sufficiency
    {n k : ℕ} (hk : 4 ≤ k) (hkn : k + 1 ≤ n)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n k)
    (mcf : MCFFeasible n k net X) :
    ∃ wit : ConvexWitness n (k + 1) X, True := by
  sorry

-- ============================================================================
-- SECTION 10: THE MAIN N&S THEOREM
-- ============================================================================

/-- Main theorem: necessary and sufficient condition for membership. -/
theorem main_ns_theorem
    {n : ℕ} (hn : n > 5)
    (X   : LayeredPoint n)
    (net : LayeredNetwork n (n - 1))
    (hMIR : ∃ F : MIRFeasible n, True)
    (hprev : ∃ wit : ConvexWitness n (n - 1) X, True) :
    (∃ wit : ConvexWitness n n X, True) ↔
    Nonempty (MCFFeasible n (n - 1) net X) := by
  constructor
  · -- Necessity
    intro ⟨wit, _⟩
    have hk : 4 ≤ n - 1 := by omega
    have hkn : n - 1 + 1 ≤ n := by omega
    have h_eq : n = (n - 1) + 1 := by omega
    exact necessity hk hkn X net (wit.cast h_eq)
  · -- Sufficiency
    intro ⟨mcf⟩
    have hk : 4 ≤ n - 1 := by omega
    have hkn : n - 1 + 1 ≤ n := by omega
    obtain ⟨wit, _⟩ := sufficiency hk hkn X net mcf
    have h_eq : (n - 1) + 1 = n := by omega
    exact ⟨wit.cast h_eq, trivial⟩

end MembershipProject.Core
