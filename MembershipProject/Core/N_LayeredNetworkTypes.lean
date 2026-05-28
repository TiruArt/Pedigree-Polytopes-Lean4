-- File No. 10 - N_LayeredNetworkTypes.lean
--
-- Layered network N_k, commodities, and MCF feasibility structure.
--
-- GLOSSARY:
--   k         : problem index for MCF(k)
--   l         : layer index, 5 ≤ l ≤ k-1 for intermediate commodity flows
--   s ∈ S_k   : commodity = arc a↔s in F_k:
--               tail s.src=(i,j,k) → head arc_head=(a,b,k+1)
--   v^s       : flow along arc a↔s = s.flow_val
--   y^s_l     : capacity used by commodity s at intermediate layer l
--   N_k       : layered network for MCF(k), nodes at layers 4..k+1
--   R_k ⊂ P_{k+1} : rigid pedigrees from frozen flows at stage k
--   zMax      : remaining flexible flow = 1 - Σ μ(P), P ∈ R_k
--
-- Reference: Arthanari, T.S. arXiv:2507.09069v1 [math.CO].

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_Types
import MembershipProject.Core.N_RestrictionFull
import MembershipProject.Core.N_PedigreeDefinition

namespace MembershipProject.Core

open Nat

-- ============================================================
-- LAYERED NETWORK N_k
-- Nodes: valid triples at layers 4..k+1.
-- Each node v has a capacity node_cap(v) > 0.
-- Arcs connect u → v when u ∈ generators(v) and u.k + 1 = v.k.
-- ============================================================

structure LayeredNetwork (n k : ℕ) where
  nodes          : Finset Triple
  node_cap       : Triple → ℚ
  cap_nn         : ∀ v ∈ nodes, node_cap v ≥ 0
  node_layers    : ∀ v ∈ nodes, 4 ≤ v.k ∧ v.k ≤ k + 1
  node_valid     : ∀ v ∈ nodes, v ∈ Delta v.k
  nodes_complete : ∀ v, 0 < node_cap v → v ∈ nodes
  node_cap_pos   : ∀ v ∈ nodes, 0 < node_cap v
  arc_valid      : ∀ u v : Triple, u ∈ nodes → v ∈ nodes →
                     u.k + 1 = v.k → u ∈ generators v
  rigid          : List (RigidEntry k)
  well_def       : nodes.Nonempty ∨ rigid ≠ []
  -- z_max_eq: total capacity = 1
  -- = Σ node_cap at layer k+1 + Σ rigid weights = 1
  z_max_eq       : (nodes.filter (fun v => v.k = k + 1)).sum node_cap +
                   rigid.foldl (fun acc e => acc + e.weight) 0 = 1

/-- zMax: the remaining flexible flow in MCF(k).
    = Σ_{v at layer k+1} node_cap(v)
    = 1 - Σ_{P ∈ R_k} μ(P)  (total weight minus rigid flows already assigned). -/
noncomputable def zMax {n k : ℕ} (net : LayeredNetwork n k) : ℚ :=
  (net.nodes.filter (fun v => v.k = k + 1)).sum net.node_cap

-- ============================================================
-- COMMODITY
-- s ∈ S_k: an arc a↔s in F_k connecting layer k to layer k+1.
--   src      = (i,j,k) ∈ Delta k    — tail of arc, at layer k
--   arc_head = (a,b,k+1) ∈ Delta(k+1) — head of arc, at layer k+1
--   flow_val = v^s > 0              — flow along arc a↔s
--
-- Arc exists because the path in N_{k-1}(L) from (1,2,3)
-- passes through a generator of arc_head (at some layer ≤ k)
-- and through src (at layer k).
-- ============================================================

structure Commodity (n k : ℕ) where
  src           : Triple
  arc_head      : Triple
  flow_val      : ℚ
  flow_pos      : flow_val > 0
  src_in_delta  : src ∈ Delta k
  head_in_delta : arc_head ∈ Delta (k + 1)

-- ============================================================
-- MCF FEASIBILITY
-- Bundles all conditions required for MCF(k) to have a
-- feasible solution, including flow conservation, capacity
-- constraints, and the precondition X/k ∈ conv(P_k).
-- k ≥ 5: MCF(k) only invoked when F_k is feasible.
-- ============================================================

structure MCFFeasible (n k : ℕ) (net : LayeredNetwork n k)
    (X : LayeredPoint n) where
  hk            : 5 ≤ k
  commodities   : List (Commodity n k)

  -- Precondition: X/k ∈ conv(P_k)
  conv_wit      : ConvexWitness n k X

  -- X satisfies MI feasibility conditions
  X_layer_sum   : ∀ l, 4 ≤ l → l ≤ k + 1 → (Delta l).sum X = 1
  X_nn          : ∀ t, X t ≥ 0
  pos_X_node    : ∀ t, X t > 0 → t ∈ net.nodes
  src_node_val  : ∀ s ∈ commodities, X s.src = 1

  -- Arc flows: f_s s u v = flow of commodity s along arc u→v
  --            f_rigid_s P s v = flow from rigid pedigree P to v
  f_s           : Commodity n k → Triple → Triple → ℚ
  f_rigid_s     : RigidEntry k → Commodity n k → Triple → ℚ

  -- Non-negativity
  f_s_nn        : ∀ s u v, f_s s u v ≥ 0
  f_rigid_s_nn  : ∀ P s v, f_rigid_s P s v ≥ 0

  -- Flow on valid arcs only
  f_s_valid     : ∀ s u v, f_s s u v > 0 → u ∈ generators v
  f_s_node      : ∀ s u v, f_s s u v > 0 → u ∈ net.nodes
  f_s_target    : ∀ s u v, f_s s u v > 0 → v ∈ net.nodes
  f_rigid_s_target : ∀ P s v, f_rigid_s P s v > 0 → v ∈ net.nodes

  -- Triangles in rigid pedigrees are valid triples
  triangles_valid : ∀ P ∈ net.rigid, ∀ t ∈ P.ped.triangles, t ∈ Delta t.k

  -- Flow conservation at intermediate nodes (layers 5..k-1)
  conservation  : ∀ s ∈ commodities, ∀ u ∈ net.nodes, u.k < k →
    (net.nodes.filter (fun w => w.k + 1 = u.k)).sum (fun w => f_s s w u) =
    (net.nodes.filter (fun w => u.k + 1 = w.k)).sum (fun w => f_s s u w)

  -- v^s = total flow from s.src to arc_head (direct + via rigid)
  flow_vals     : ∀ s ∈ commodities, s.flow_val =
    (Delta (k + 1)).sum (fun v => f_s s s.src v) +
    net.rigid.foldl (fun acc P =>
      acc + (Delta (k + 1)).sum (fun v => f_rigid_s P s v)) 0

  -- Layer sum: Σ_{arcs in F_l} y^s(arc) = v^s, for 4 ≤ l ≤ k
  layer_sum     : ∀ s ∈ commodities, ∀ l, 4 ≤ l → l ≤ k →
    (Delta l).sum (fun t =>
      (Delta (t.k + 1)).sum (fun v => f_s s t v) +
      net.rigid.foldl (fun acc P =>
        acc + if t ∈ P.ped.triangles then
          (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
        else 0) 0) = s.flow_val

  -- MCF Property 1: flow through node t bounded by available slack
  -- y^s_q(t) ≤ gen_sum(t) − Σ_{l=j₀+1}^{q-1} y^s_l(i₀,j₀)
  flow_le_slack : ∀ s ∈ commodities, ∀ q, 4 ≤ q → q ≤ k →
    ∀ t ∈ Delta q,
    (Delta (t.k + 1)).sum (fun v => f_s s t v) +
    net.rigid.foldl (fun acc P =>
      acc + if t ∈ P.ped.triangles then
        (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
      else 0) 0 ≤
    (generators t).sum (fun t' =>
      (Delta (t'.k + 1)).sum (fun v => f_s s t' v) +
      net.rigid.foldl (fun acc P =>
        acc + if t' ∈ P.ped.triangles then
          (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
        else 0) 0) -
    (Finset.Ico (t.j + 1) q).sum (fun l =>
      (Delta l).sum (fun u =>
        if u.i = t.i ∧ u.j = t.j then
          (Delta (u.k + 1)).sum (fun v => f_s s u v) +
          net.rigid.foldl (fun acc P =>
             acc + if u ∈ P.ped.triangles then
              (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
            else 0) 0
        else 0))

  -- MCF Property 2: available slack always non-negative
  slack_nonneg  : ∀ s ∈ commodities, ∀ q, 4 ≤ q → q ≤ k →
    ∀ t ∈ Delta q,
    (generators t).sum (fun t' =>
      (Delta (t'.k + 1)).sum (fun v => f_s s t' v) +
      net.rigid.foldl (fun acc P =>
        acc + if t' ∈ P.ped.triangles then
          (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
        else 0) 0) -
    (Finset.Ico (t.j + 1) q).sum (fun l =>
      (Delta l).sum (fun u =>
        if u.i = t.i ∧ u.j = t.j then
          (Delta (u.k + 1)).sum (fun v => f_s s u v) +
          net.rigid.foldl (fun acc P =>
            acc + if u ∈ P.ped.triangles then
              (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
            else 0) 0
        else 0)) ≥ 0

  -- ============================================================
  -- FIELDS FOR Y ∈ conv(P_{k+1})
  -- Used in proving sufficiency: X/(k+1) ∈ conv(P_{k+1}).
  -- ============================================================

  -- Tail and head of each commodity arc are in the network
  src_in_net    : ∀ s ∈ commodities, s.src ∈ net.nodes
  head_in_net   : ∀ s ∈ commodities, s.arc_head ∈ net.nodes

  -- arc_head is genuinely new at layer k+1:
  -- no node at layer < k+1 shares (i,j) with arc_head
  ext_new       : ∀ s ∈ commodities, ∀ v ∈ net.nodes,
                    v.k < k + 1 →
                    v.i ≠ s.arc_head.i ∨ v.j ≠ s.arc_head.j

  -- Normalized: X(arc_head) = 1 for each commodity
  src_val       : ∀ s ∈ commodities, X s.arc_head = 1

  -- Total commodity flow = zMax (all flexible flow accounted for)
  flow_is_zMax  : commodities.foldl (fun acc s => acc + s.flow_val) 0 = zMax net

  -- All commodity flow passes through source node (1,2,3)
  source_flow   : ∀ s ∈ commodities,
    (Delta 4).sum (fun v => f_s s (1, 2, 3) v) +
    net.rigid.foldl (fun acc P => acc + if (1, 2, 3) ∈ P.ped.triangles then
      (Delta (k + 1)).sum (fun v => f_rigid_s P s v) else 0) 0 = s.flow_val

  -- Column sum: total flow through edge (a,b) ≤ v^s
  col_sum_le    : ∀ s ∈ commodities, ∀ a b : ℕ,
    (Finset.Ico 4 (k + 1)).sum (fun l =>
      (Delta (l + 1)).sum (fun v => f_s s (a, b, l) v) +
      net.rigid.foldl (fun acc P => acc + if (a, b, l) ∈ P.ped.triangles then
        (Delta (k + 1)).sum (fun v => f_rigid_s P s v) else 0) 0) +
    (f_s s s.src (a, b, k + 1) +
     net.rigid.foldl (fun acc P => acc + f_rigid_s P s (a, b, k + 1)) 0)
    ≤ s.flow_val

  -- When N_k = ∅, X is fully determined by rigid pedigrees
  rigid_combo   : net.nodes = ∅ → ∀ t, t.k ≤ k + 1 →
    net.rigid.foldl (fun acc P =>
      acc + P.weight * if t ∈ P.ped.triangles then 1 else 0) 0 = X t

end MembershipProject.Core
