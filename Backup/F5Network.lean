-- Core/F5Network.lean
-- F5 Network construction with Python max-flow integration

import MembershipProject.Core.GraphInterface
import MembershipProject.Core.RestrictionFull

-- Node type (i, j, k) where 1 ≤ i < j < k ≤ n
abbrev Node := Nat × Nat × Nat

-- Pedigree path of length k
structure PedigreePath (k : Nat) where
  path : List Nat
  length_eq : path.length = k + 1

-- F5 Network structure with two types of arcs
structure F5Network where
  -- Source nodes from layer 5
  sourceNodes : List (Node × Rat)
  -- Pedigree sources from R₄
  pedigreeSources : List (PedigreePath 4 × Rat)
  -- Sink nodes in layer 6
  sinkNodes : List (Node × Rat)
  -- Arcs from layer 5 to layer 6 with capacity C(L)
  arcs : List (Node × Node × Rat)
  -- Arcs from pedigrees to layer 6 with capacity μ(P)
  pedigreeArcs : List (PedigreePath 4 × Node × Rat)

-- ========== Python External Routines ==========

-- Convert Rational to String for Python (e.g., "3/4")
def ratToString (r : Rat) : String :=
  s!"{r.num}/{r.den}"

-- Parse String from Python back to Rational
def parseRational (s : String) : Option Rat :=
  match s.splitOn "/" with
  | [num, den] =>
      match (num.toNat?, den.toNat?) with
      | (some n, some d) =>
          if d = 0 then none
          else some (Rat.mk n d)
      | _ => none
  | _ => none

-- Python binding for max-flow computation
-- Calls: maxflowwithnodecaps.compute_max_flow(nodes, edges, source, sink)
@[extern "compute_max_flow_from_lean"]
opaque computeMaxFlowPython
  (nodes : List (Node × String × Nat))  -- (node, capacity_str, layer)
  (edges : List (Node × Node × String)) -- (u, v, capacity_str)
  (source : Node)
  (sink : Node) : String                 -- Returns "numerator/denominator"

-- Wrapper that handles Rat conversion
def computeMaxFlow
  (nodes : List (Node × Rat × Nat))
  (edges : List (Node × Node × Rat))
  (source : Node)
  (sink : Node) : Option Rat :=
  let nodesStr := nodes.map (fun (n, cap, layer) => (n, ratToString cap, layer))
  let edgesStr := edges.map (fun (u, v, cap) => (u, v, ratToString cap))
  let result := computeMaxFlowPython nodesStr edgesStr source sink
  parseRational result

-- ========== Helper Functions ==========

-- Convert Node to Triple (with proof obligations)
def nodeToTriple? (n : Node) : Option Triple :=
  let (i, j, k) := n
  if h1 : i < j then
    if h2 : j < k then
      some ⟨i, j, k, h1, h2⟩
    else none
  else none

-- Convert Triple back to Node
def tripleToNode (t : Triple) : Node :=
  (t.i, t.j, t.k)

-- ========== Network Construction ==========

-- Build N₄(L) by deleting restriction set D and adding link L
def constructRestrictedNetwork
  (N₄_nodes : List (Node × Rat × Nat))
  (N₄_edges : List (Node × Node × Rat))
  (L : Node × Node) : (List (Node × Rat × Nat) × List (Node × Node × Rat)) :=
  let (srcNode, tgtNode) := L
  match nodeToTriple? srcNode, nodeToTriple? tgtNode with
  | some t1, some t2 =>
      -- Compute restriction set D
      let D := Restriction.computeD t1 t2
      let nodesToDelete := D.map tripleToNode
      let deleteSet := nodesToDelete.toFinset

      -- Filter out nodes in D
      let nodes_restricted := N₄_nodes.filter (fun (n, _, _) => n ∉ deleteSet)

      -- Filter out edges involving nodes in D
      let edges_restricted := N₄_edges.filter (fun (u, v, _) =>
        u ∉ deleteSet ∧ v ∉ deleteSet)

      -- Add link L with capacity 1
      let edges_with_link := (srcNode, tgtNode, 1) :: edges_restricted

      (nodes_restricted, edges_with_link)
  | _, _ => (N₄_nodes, N₄_edges)  -- Invalid nodes, return original

-- Compute link capacity C(L) = max-flow in N₄(L)
def computeLinkCapacity
  (N₄_nodes : List (Node × Rat × Nat))
  (N₄_edges : List (Node × Node × Rat))
  (L : Node × Node) : Option Rat :=
  let (srcNode, tgtNode) := L
  let (nodes_restricted, edges_restricted) := constructRestrictedNetwork N₄_nodes N₄_edges L
  computeMaxFlow nodes_restricted edges_restricted srcNode tgtNode

-- ========== F5 Network Builder ==========

-- Extract layer 5 nodes from N₄
def getLayer5Nodes (N₄_nodes : List (Node × Rat × Nat)) : List (Node × Rat) :=
  N₄_nodes.filter (fun (_, _, layer) => layer = 5)
    |>.map (fun (n, cap, _) => (n, cap))

-- Extract layer 6 nodes from N₄
def getLayer6Nodes (N₄_nodes : List (Node × Rat × Nat)) : List (Node × Rat) :=
  N₄_nodes.filter (fun (_, _, layer) => layer = 6)
    |>.map (fun (n, cap, _) => (n, cap))

-- Get all potential links L from layer 5 to layer 6
def getPotentialLinks
  (layer5 : List (Node × Rat))
  (layer6 : List (Node × Rat)) : List (Node × Node) :=
  layer5.bind (fun (src, _) =>
    layer6.map (fun (tgt, _) => (src, tgt)))

-- Build F5 network arcs with computed capacities
def buildF5Arcs
  (N₄_nodes : List (Node × Rat × Nat))
  (N₄_edges : List (Node × Node × Rat))
  (links : List (Node × Node)) : List (Node × Node × Rat) :=
  links.filterMap (fun L =>
    match computeLinkCapacity N₄_nodes N₄_edges L with
    | some capacity =>
        let (src, tgt) := L
        some (src, tgt, capacity)
    | none => none)

-- Build pedigree arcs from R₄ to layer 6
def buildPedigreeArcs
  (R₄ : List (PedigreePath 4 × Rat))
  (layer6 : List (Node × Rat)) : List (PedigreePath 4 × Node × Rat) :=
  R₄.bind (fun (P, mu) =>
    -- For each pedigree P, find compatible layer 6 nodes
    -- (This depends on your pedigree compatibility rules)
    layer6.filterMap (fun (n, _) =>
      -- Check if pedigree P is compatible with node n
      -- For now, placeholder: connect to all layer 6 nodes
      some (P, n, mu)))

-- Main F5 network builder
def buildF5Network
  (N₄_nodes : List (Node × Rat × Nat))
  (N₄_edges : List (Node × Node × Rat))
  (R₄ : List (PedigreePath 4 × Rat)) : F5Network :=
  let layer5 := getLayer5Nodes N₄_nodes
  let layer6 := getLayer6Nodes N₄_nodes
  let potentialLinks := getPotentialLinks layer5 layer6
  let arcs := buildF5Arcs N₄_nodes N₄_edges potentialLinks
  let pedigreeArcs := buildPedigreeArcs R₄ layer6
  {
    sourceNodes := layer5,
    pedigreeSources := R₄,
    sinkNodes := layer6,
    arcs := arcs,
    pedigreeArcs := pedigreeArcs
  }

-- ========== Export Max-Flow for Direct Use ==========

-- Compute max-flow on F5 network (for final polytope computation)
def computeF5MaxFlow
  (f5 : F5Network)
  (supersource : Node)
  (supersink : Node) : Option Rat :=
  -- Convert F5Network to node/edge lists
  -- Add supersource connected to all sourceNodes and pedigreeSources
  -- Add supersink connected from all sinkNodes
  -- This is a placeholder - implement based on your F5 structure
  sorry
