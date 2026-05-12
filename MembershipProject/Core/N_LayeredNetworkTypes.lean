--- Core/N_LayeredNetworkTypes.lean
-- Layered network, commodities, MCF feasibility.
-- Triple = ℕ × ℕ × ℕ.
--
-- GLOSSARY (Chapter 5):
-- k         : problem index for MCF(k)
-- l         : layer index, 5 ≤ l ≤ k-1 for intermediate commodity flows
-- s ∈ S_k   : commodity = arc a ↔ s in F_k: tail s.src=(i,j,k) → head arc_head=(a,b,k+1)
-- v^s       : flow along arc a ↔ s = s.flow_val
-- y^s_l     : capacity used by commodity s at intermediate layer l, 5 ≤ l ≤ k-1
-- N_k       : layered network for MCF(k), nodes at layers 4..k+1
-- R_k ⊂ P_{k+1} : rigid pedigrees from frozen flows at stage k
-- zMax      : remaining flexible flow = 1 - ∑ μ(R_k)

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_Types
import MembershipProject.Core.N_RestrictionFull
import MembershipProject.Core.N_PedigreeDefinition
namespace MembershipProject.Core

open Nat

-- ============================================================
-- LAYERED NETWORK N_k
-- nodes: Finset Triple  (all valid triples at layers 4..k+1)
-- ============================================================

structure LayeredNetwork (n k : ℕ) where
  nodes        : Finset Triple
  node_cap     : Triple → ℚ
  cap_nn       : ∀ v ∈ nodes, node_cap v ≥ 0
  node_layers  : ∀ v ∈ nodes, 4 ≤ v.k ∧ v.k ≤ k + 1  -- nodes at layers 4..k+1
  node_valid   : ∀ v ∈ nodes, v ∈ Delta v.k            -- every node is a valid triple
  nodes_complete : ∀ v, 0 < node_cap v → v ∈ nodes     -- positive capacity → in nodes
  node_cap_pos   : ∀ v ∈ nodes, 0 < node_cap v         -- every node has positive capacity
  arc_valid    : ∀ u v : Triple, u ∈ nodes → v ∈ nodes →
                   u.k + 1 = v.k → u ∈ generators v
  rigid        : List (RigidEntry k)
  well_def     : nodes.Nonempty ∨ rigid ≠ []
  z_max_eq     : (nodes.filter (fun v => v.k = k + 1)).sum node_cap +
                 rigid.foldl (fun acc e => acc + e.weight) 0 = 1

-- zMax = maximum possible total flow in MCF(k) given R_k
-- = Σ_{v at k+1} node_cap v = 1 - Σ_{P ∈ R_k} μ(P)
-- (total weight minus rigid flows already assigned)
noncomputable def zMax {n k : ℕ} (net : LayeredNetwork n k) : ℚ :=
  (net.nodes.filter (fun v => v.k = k + 1)).sum net.node_cap

-- ============================================================
-- COMMODITY
-- s ∈ S_k: arc a ↔ s in F_k
--   tail: s.src = (i,j,k) ∈ Delta k
--   head: s.arc_head = (a,b,k+1) ∈ Delta (k+1)
--   s.src ∈ generators s.arc_head
-- ============================================================

structure Commodity (n k : ℕ) where
  src           : Triple          -- tail of arc a ↔ s, at layer k
  arc_head      : Triple          -- head of arc a ↔ s, at layer k+1
  flow_val      : ℚ               -- v^s = flow along arc a ↔ s
  flow_pos      : flow_val > 0
  src_in_delta  : src ∈ Delta k             -- s.src ∈ Delta k
  head_in_delta : arc_head ∈ Delta (k + 1)  -- arc_head ∈ Delta (k+1)
  -- Arc exists because path in N_{k-1}(L) from (1,2,3) passes through
  -- a generator of arc_head (at some layer L ≤ k) and src (at layer k)

-- ============================================================
-- MCF FEASIBILITY
-- ============================================================

structure MCFFeasible (n k : ℕ) (net : LayeredNetwork n k)
    (X : LayeredPoint n) where
  hk                : 5 ≤ k   -- MCF(k) only invoked when F_k feasible, k ≥ 5
  commodities       : List (Commodity n k)

  -- X/k ∈ conv(P_k) — precondition for MCF(k) feasibility
  conv_wit          : ConvexWitness n k X

  -- X satisfies preconditions for MCF feasibility
  X_layer_sum       : ∀ l, 4 ≤ l → l ≤ k + 1 → (Delta l).sum X = 1
  X_nn              : ∀ t, X t ≥ 0
  -- Any node with positive X value is in the network
  pos_X_node        : ∀ t, X t > 0 → t ∈ net.nodes
  -- X places unit weight at s.src for each commodity s
  src_node_val      : ∀ s ∈ commodities, X s.src = 1

  -- Arc flows
  f_s               : Commodity n k → Triple → Triple → ℚ
  f_rigid_s         : RigidEntry k → Commodity n k → Triple → ℚ

  -- Non-negativity
  f_s_nn            : ∀ s u v, f_s s u v ≥ 0
  f_rigid_s_nn      : ∀ P s v, f_rigid_s P s v ≥ 0

  -- Flow on valid arcs only; both source and target nodes are in network
  f_s_valid         : ∀ s u v, f_s s u v > 0 → u ∈ generators v
  f_s_node          : ∀ s u v, f_s s u v > 0 → u ∈ net.nodes
  f_s_target        : ∀ s u v, f_s s u v > 0 → v ∈ net.nodes
  -- Rigid flow target is in network
  f_rigid_s_target  : ∀ P s v, f_rigid_s P s v > 0 → v ∈ net.nodes

  -- Triangles in rigid pedigrees are valid triples
  triangles_valid   : ∀ P ∈ net.rigid, ∀ t ∈ P.ped.triangles, t ∈ Delta t.k

  -- Flow conservation at intermediate nodes (layers 5..k-1)
  conservation      : ∀ s ∈ commodities, ∀ u ∈ net.nodes, u.k < k →
    (net.nodes.filter (fun w => w.k + 1 = u.k)).sum (fun w => f_s s w u) =
    (net.nodes.filter (fun w => u.k + 1 = w.k)).sum (fun w => f_s s u w)

  -- Flow values: v^s = flow from s.src to arc_head
  flow_vals         : ∀ s ∈ commodities, s.flow_val =
    (Delta (k + 1)).sum (fun v => f_s s s.src v) +
    net.rigid.foldl (fun acc P =>
      acc + (Delta (k + 1)).sum (fun v => f_rigid_s P s v)) 0

  -- Layer sum: ∑_{arcs in F_l} y^s(arc) = v^s  (4 ≤ l ≤ k)
  -- l=4: F_4 feasibility ensures conservation at layer 4
  -- l=5..k-1: intermediate layers, conservation
  -- l=k: s.src is the unique node, all v^s flows through it
  layer_sum         : ∀ s ∈ commodities, ∀ l, 4 ≤ l → l ≤ k →
    (Delta l).sum (fun t =>
      (Delta (t.k + 1)).sum (fun v => f_s s t v) +
      net.rigid.foldl (fun acc P =>
        acc + if t ∈ P.ped.triangles then
          (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
        else 0) 0) = s.flow_val

  -- DIRECT MCF PROPERTY 1:
  -- Flow y^s_q(u) through node u at layer q bounded by available slack
  -- y^s_q(u) ≤ gen_sum(u) − ∑_{l=j₀+1}^{q-1} y^s_l(i₀,j₀)
  flow_le_slack      : ∀ s ∈ commodities, ∀ q, 4 ≤ q → q ≤ k →
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

  -- DIRECT MCF PROPERTY 2:
  -- Slack always nonneg: generator inflow ≥ intermediate consumption
  slack_nonneg       : ∀ s ∈ commodities, ∀ q, 4 ≤ q → q ≤ k →
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
  -- FIELDS FOR Ysinconv (Chapter 5, Lemma Ysinconv)
  -- ============================================================

  -- Both tail and head of arc a ↔ s are in the network (MCF construction)
  src_in_net        : ∀ s ∈ commodities, s.src ∈ net.nodes
  head_in_net       : ∀ s ∈ commodities, s.arc_head ∈ net.nodes

  -- No network node at layer < k+1 shares (i,j) with arc_head
  -- (arc_head is genuinely new at layer k+1)
  ext_new           : ∀ s ∈ commodities, ∀ v ∈ net.nodes,
                        v.k < k + 1 →
                        v.i ≠ s.arc_head.i ∨ v.j ≠ s.arc_head.j

  -- Normalized flow to arc_head equals 1 (v^s / v^s = 1)
  src_val           : ∀ s ∈ commodities, X s.arc_head = 1

  -- Total flow = z_max
  flow_is_zMax        :
    commodities.foldl (fun acc s => acc + s.flow_val) 0 = zMax net

  -- Flow from initial node (1,2,3) = v^s (all commodity flow passes through source)
  source_flow       : ∀ s ∈ commodities,
    (Delta 4).sum (fun v => f_s s (1, 2, 3) v) +
    net.rigid.foldl (fun acc P => acc + if (1, 2, 3) ∈ P.ped.triangles then
      (Delta (k + 1)).sum (fun v => f_rigid_s P s v) else 0) 0 = s.flow_val

  -- Column sum: total flow through (a,b) at layers 4..k plus top layer ≤ v^s
  col_sum_le        : ∀ s ∈ commodities, ∀ a b : ℕ,
    (Finset.Ico 4 (k + 1)).sum (fun l =>
      (Delta (l + 1)).sum (fun v => f_s s (a, b, l) v) +
      net.rigid.foldl (fun acc P => acc + if (a, b, l) ∈ P.ped.triangles then
        (Delta (k + 1)).sum (fun v => f_rigid_s P s v) else 0) 0) +
    (f_s s s.src (a, b, k + 1) +
     net.rigid.foldl (fun acc P => acc + f_rigid_s P s (a, b, k + 1)) 0)
    ≤ s.flow_val

  -- When N_k = ∅, X determined by rigid pedigrees
  rigid_combo       : net.nodes = ∅ → ∀ t, t.k ≤ k + 1 →
    net.rigid.foldl (fun acc P =>
      acc + P.weight * if t ∈ P.ped.triangles then 1 else 0) 0 = X t

end MembershipProject.Core
