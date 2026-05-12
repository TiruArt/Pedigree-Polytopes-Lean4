-- Core/N_LayeredNetworkTypes.lean
-- Layered network, commodities, MCF feasibility.

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_Types
import MembershipProject.Core.N_RestrictionFull

namespace MembershipProject.Core

open Nat

structure LayeredNetwork (n k : ℕ) where
  nodes        : Finset Triple
  node_cap     : Triple → ℚ
  cap_nn       : ∀ v ∈ nodes, node_cap v ≥ 0
  node_layers  : ∀ v ∈ nodes, 4 ≤ v.k ∧ v.k ≤ k
  node_valid   : ∀ v ∈ nodes, v ∈ Delta v.k
  arc_valid    : ∀ u v : Triple, u ∈ nodes → v ∈ nodes →
                   u.k + 1 = v.k → u ∈ generators v
  rigid        : List (RigidEntry n)
  -- All triangles in rigid pedigrees are at layers ≤ k
  rigid_layers : ∀ P ∈ rigid, ∀ t ∈ P.triangles, t.k ≤ k
  well_def     : nodes.Nonempty ∨ rigid ≠ []
  z_max_eq     : (nodes.filter (fun v => v.k = k)).sum node_cap +
                 rigid.foldl (fun acc e => acc + e.weight) 0 = 1

noncomputable def zMax {n k : ℕ} (net : LayeredNetwork n k) : ℚ :=
  (net.nodes.filter (fun v => v.k = k)).sum net.node_cap +
  net.rigid.foldl (fun acc e => acc + e.weight) 0

structure Commodity (n k : ℕ) where
  src      : Triple
  flow_val : ℚ
  flow_pos : flow_val > 0

structure MCFFeasible (n k : ℕ) (net : LayeredNetwork n k)
    (X : LayeredPoint n) where
  commodities       : List (Commodity n k)
  f_s               : Commodity n k → Triple → Triple → ℚ
  f_rigid_s         : RigidEntry n → Commodity n k → Triple → ℚ
  f_s_nn            : ∀ s u v, f_s s u v ≥ 0
  f_rigid_s_nn      : ∀ P s v, f_rigid_s P s v ≥ 0
  f_s_valid         : ∀ s u v, f_s s u v > 0 → u ∈ generators v
  f_s_node          : ∀ s u v, f_s s u v > 0 → u ∈ net.nodes
  -- Triangles in rigid pedigrees are valid triples
  triangles_valid   : ∀ P ∈ net.rigid, ∀ t ∈ P.triangles, t ∈ Delta t.k
  conservation      : ∀ s ∈ commodities, ∀ u ∈ net.nodes, u.k < k →
    (net.nodes.filter (fun w => w.k + 1 = u.k)).sum (fun w => f_s s w u) =
    (net.nodes.filter (fun w => u.k + 1 = w.k)).sum (fun w => f_s s u w)
  flow_vals         : ∀ s ∈ commodities, s.flow_val =
    (Delta (k + 1)).sum (fun v => f_s s s.src v) +
    net.rigid.foldl (fun acc P =>
      acc + (Delta (k + 1)).sum (fun v => f_rigid_s P s v)) 0
  -- Root flow: all flow of commodity s passes through (1,2,3)
  root_flow         : ∀ s ∈ commodities,
    (Delta 4).sum (fun v => f_s s (1, 2, 3) v) +
    net.rigid.foldl (fun acc P =>
      acc + if (1, 2, 3) ∈ P.triangles then
        (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
      else 0) 0 = s.flow_val
  layer_sum         : ∀ s ∈ commodities, ∀ l, 4 ≤ l → l ≤ k →
    (Delta l).sum (fun t =>
      (Delta (t.k + 1)).sum (fun v => f_s s t v) +
      net.rigid.foldl (fun acc P =>
        acc + if t ∈ P.triangles then
          (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
        else 0) 0) = s.flow_val
  flow_le_slack     : ∀ s ∈ commodities, ∀ q, 4 ≤ q → q ≤ k →
    ∀ t ∈ Delta q,
    (Delta (t.k + 1)).sum (fun v => f_s s t v) +
    net.rigid.foldl (fun acc P =>
      acc + if t ∈ P.triangles then
        (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
      else 0) 0 ≤
    (generators t).sum (fun t' =>
      (Delta (t'.k + 1)).sum (fun v => f_s s t' v) +
      net.rigid.foldl (fun acc P =>
        acc + if t' ∈ P.triangles then
          (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
        else 0) 0) -
    (Finset.Ico (t.j + 1) q).sum (fun l =>
      (Delta l).sum (fun u =>
        if u.i = t.i ∧ u.j = t.j then
          (Delta (u.k + 1)).sum (fun v => f_s s u v) +
          net.rigid.foldl (fun acc P =>
            acc + if u ∈ P.triangles then
              (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
            else 0) 0
        else 0))
  slack_nonneg      : ∀ s ∈ commodities, ∀ q, 4 ≤ q → q ≤ k →
    ∀ t ∈ Delta q,
    (generators t).sum (fun t' =>
      (Delta (t'.k + 1)).sum (fun v => f_s s t' v) +
      net.rigid.foldl (fun acc P =>
        acc + if t' ∈ P.triangles then
          (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
        else 0) 0) -
    (Finset.Ico (t.j + 1) q).sum (fun l =>
      (Delta l).sum (fun u =>
        if u.i = t.i ∧ u.j = t.j then
          (Delta (u.k + 1)).sum (fun v => f_s s u v) +
          net.rigid.foldl (fun acc P =>
            acc + if u ∈ P.triangles then
              (Delta (k + 1)).sum (fun v => f_rigid_s P s v)
            else 0) 0
        else 0)) ≥ 0
  total_flow        :
    commodities.foldl (fun acc s => acc + s.flow_val) 0 = zMax net

end MembershipProject.Core
