-- Core/UptoF_{5}.lean
-- ========================================================
-- F₄, N₄, N₄(L), and F₅ Network Visualization
-- Paper: "A Strongly Polynomial Algorithm for Membership
--        in the Pedigree Polytope" by Tiru Arthanari
-- Section 4: Layered Network Construction Examples
-- ========================================================

import Mathlib.Data.Rat.Defs
--import Mathlib.Data.Rat.Order
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Algebra.Order.Ring.Rat

namespace F5Visualization

-- [Rest of visualization code...]

/-! ## Network Visualization for Test Case

Given X with coordinates:
* x₄: (1,3,4) = 3/4, (2,3,4) = 1/4
* x₅: (1,2,5) = 1/2, (3,4,5) = 1/2
* x₆: (1,3,6) = 1/4, (2,3,6) = 1/4, (2,4,6) = 1/4, (3,4,6) = 1/4

This module visualizes the network structures at each stage.
-/

-- ============================================
-- DATA STRUCTURES
-- ============================================

structure Node where
  i : Nat
  j : Nat
  k : Nat
deriving Repr, DecidableEq, BEq

instance : ToString Node where
  toString n := s!"({n.i},{n.j},{n.k})"

structure Edge where
  source : Node
  target : Node
  capacity : Rat
deriving Repr

instance : ToString Edge where
  toString e := s!"{e.source} → {e.target} [cap: {e.capacity}]"

structure Network where
  nodes : List (Node × Rat)  -- (node, capacity)
  edges : List Edge
deriving Repr

-- ============================================
-- ARC VALIDITY RULES
-- ============================================

/-- Arc rule: (i,j,4) → (a,b,5) -/
def validArc_4_to_5 (i j a b : Nat) : Bool :=
  (i ≠ a ∨ j ≠ b) ∧ (b ≤ 3 ∨ (b > 3 ∧ (a = i ∨ a = j)))

/-- Arc rule: (i,j,5) → (a,b,6) -/
def validArc_5_to_6 (i j a b : Nat) : Bool :=
  (i ≠ a ∨ j ≠ b) ∧ (b ≤ 4 ∨ (b > 4 ∧ (a = i ∨ a = j)))

-- ============================================
-- F₄ NETWORK CONSTRUCTION
-- ============================================

def buildF4Network (x4 x5 : List (Node × Rat)) : Network :=
  let source : Node := { i := 1, j := 2, k := 3 }
  let sink : Node := { i := 0, j := 0, k := 99 }

  -- All nodes
  let nodes := [(source, (1 : Rat))] ++ x4 ++ x5 ++ [(sink, (1 : Rat))]

  -- Source → T₄ edges
  let source_edges := x4.map fun (n4, _) =>
    { source := source, target := n4, capacity := 1000 : Edge }

  -- T₄ → T₅ edges
  let t4_t5_edges := x4.bind fun (n4, _) =>
    x5.filterMap fun (n5, _) =>
      if validArc_4_to_5 n4.i n4.j n5.i n5.j then
        some { source := n4, target := n5, capacity := 1000 : Edge }
      else none

  -- T₅ → sink edges
  let sink_edges := x5.map fun (n5, _) =>
    { source := n5, target := sink, capacity := 1000 : Edge }

  { nodes := nodes,
    edges := source_edges ++ t4_t5_edges ++ sink_edges }

-- ============================================
-- N₄ NETWORK (after subtracting rigid flows)
-- ============================================

/-- For visualization, assume no rigid pedigrees (simplified) -/
def buildN4Network (x4 x5 : List (Node × Rat)) : Network :=
  buildF4Network x4 x5

-- ============================================
-- N₄(L) RESTRICTED NETWORK
-- ============================================

/-- Build N₄(L) for link L = src_node → tgt_node
    Restriction: Delete all T₅ nodes except src_node
-/
def buildN4_L (n4 : Network) (src_node : Node) (x5 : List (Node × Rat)) : Network :=
  -- Nodes to keep: everything except other T₅ nodes
  let nodes_to_keep := n4.nodes.filter fun (n, _) =>
    n.k ≠ 5 ∨ n == src_node

  -- Edges: only those between remaining nodes
  let remaining_nodes := nodes_to_keep.map Prod.fst
  let edges_to_keep := n4.edges.filter fun e =>
    remaining_nodes.contains e.source && remaining_nodes.contains e.target

  { nodes := nodes_to_keep, edges := edges_to_keep }

-- ============================================
-- F₅ NETWORK CONSTRUCTION
-- ============================================

structure RigidPedigree where
  t4_node : Node
  t5_node : Node
  flow : Rat
deriving Repr

/-- Build F₅ bipartite network -/
def buildF5Network (x5 x6 : List (Node × Rat))
    (r4 : List RigidPedigree)
    (link_caps : List ((Node × Node) × Rat)) : Network :=

  -- Virtual source nodes (one per rigid pedigree)
  let virtual_sources := r4.enum.map fun (idx, rp) =>
    ({ i := 100 + idx, j := 100 + idx, k := 0 }, rp.flow)

  -- T₅ and T₆ nodes
  let nodes := virtual_sources ++ x5 ++ x6

  -- Virtual source → T₆ edges
  let vs_edges := r4.enum.bind fun (idx, rp) =>
    let vs_node : Node := { i := 100 + idx, j := 100 + idx, k := 0 }
    x6.filterMap fun (n6, _) =>
      if validArc_5_to_6 rp.t5_node.i rp.t5_node.j n6.i n6.j then
        some { source := vs_node, target := n6, capacity := rp.flow : Edge }
      else none

  -- T₅ → T₆ edges (with computed capacities)
  let t5_t6_edges := link_caps.filterMap fun ((n5, n6), cap) =>
    if cap > 0 then
      some { source := n5, target := n6, capacity := cap : Edge }
    else none

  { nodes := nodes, edges := vs_edges ++ t5_t6_edges }

-- ============================================
-- VISUALIZATION / PRINTING
-- ============================================

def printNode (n : Node) : String :=
  if n.k == 99 then "sink"
  else if n.k == 0 then s!"VS{n.i - 100}"
  else s!"({n.i},{n.j},{n.k})"

def printEdge (e : Edge) : String :=
  s!"  {printNode e.source} → {printNode e.target} [cap: {e.capacity}]"

def printNetwork (net : Network) (title : String) : IO Unit := do
  IO.println s!"\n{String.mk (List.replicate 60 '=')}"
  IO.println title
  IO.println s!"{String.mk (List.replicate 60 '=')}"

  IO.println s!"\nNodes: {net.nodes.length}"
  for (node, cap) in net.nodes do
    IO.println s!"  {printNode node}: capacity = {cap}"

  IO.println s!"\nEdges: {net.edges.length}"
  for edge in net.edges do
    IO.println (printEdge edge)

-- ============================================
-- DETAILED ANALYSIS
-- ============================================

def analyzeF4 (net : Network) (x4 x5 : List (Node × Rat)) : IO Unit := do
  IO.println "\nF₄ Network Analysis:"

  let source_edges := net.edges.filter fun e => e.source.k == 3
  IO.println s!"  Source → T₄: {source_edges.length} edges"

  let t4_t5_edges := net.edges.filter fun e =>
    e.source.k == 4 && e.target.k == 5
  IO.println s!"  T₄ → T₅: {t4_t5_edges.length} edges"

  IO.println "\n  T₄ → T₅ Connectivity Matrix:"
  for (n4, _) in x4 do
    let targets := (t4_t5_edges.filter (fun e => e.source == n4)).map
      (fun e => printNode e.target)
    IO.println s!"    {printNode n4} → {targets}"

def analyzeN4_L (net : Network) (src_node tgt_node : Node) (x5 : List (Node × Rat)) : IO Unit := do
  IO.println s!"\nN₄(L) for L = {printNode src_node} → {printNode tgt_node}:"
  IO.println s!"  Restriction: Delete all T₅ nodes except {printNode src_node}"

  let deleted := (x5.filter (fun (n, _) => n ≠ src_node)).map Prod.fst
  IO.println s!"  Deleted nodes: {deleted.map printNode}"
  IO.println s!"  Remaining edges: {net.edges.length}"

def analyzeF5 (net : Network) (r4 : List RigidPedigree) : IO Unit := do
  IO.println "\nF₅ Network Analysis:"
  IO.println s!"  Virtual sources (R₄): {r4.length}"

  for (idx, rp) in r4.enum do
    IO.println s!"\n  VS{idx}: (1,2,3)→{printNode rp.t4_node}→{printNode rp.t5_node}"
    IO.println s!"         μ(P) = {rp.flow}"

    let vs_node : Node := { i := 100 + idx, j := 100 + idx, k := 0 }
    let vs_edges := net.edges.filter (fun e => e.source == vs_node)
    IO.println s!"         Reaches {vs_edges.length} T₆ nodes:"
    for e in vs_edges do
      IO.println s!"           → {printNode e.target}"

-- ============================================
-- MAIN DEMO
-- ============================================

def testData : IO Unit := do
  -- Test data
  let x4 : List (Node × Rat) := [
    ({ i := 1, j := 3, k := 4 }, 3/4),
    ({ i := 2, j := 3, k := 4 }, 1/4)
  ]

  let x5 : List (Node × Rat) := [
    ({ i := 1, j := 2, k := 5 }, 1/2),
    ({ i := 3, j := 4, k := 5 }, 1/2)
  ]

  let x6 : List (Node × Rat) := [
    ({ i := 1, j := 3, k := 6 }, 1/4),
    ({ i := 2, j := 3, k := 6 }, 1/4),
    ({ i := 2, j := 4, k := 6 }, 1/4),
    ({ i := 3, j := 4, k := 6 }, 1/4)
  ]

  -- Build and show F₄
  let f4 := buildF4Network x4 x5
  printNetwork f4 "F₄ Network (Initial)"
  analyzeF4 f4 x4 x5

  -- Build and show N₄
  let n4 := buildN4Network x4 x5
  printNetwork n4 "N₄ Network (After Subtracting Rigid Flows)"

  -- Show example N₄(L) networks
  let link1 := ({ i := 1, j := 2, k := 5 }, { i := 1, j := 3, k := 6 })
  let n4_l1 := buildN4_L n4 link1.1 x5
  printNetwork n4_l1 s!"N₄(L) for L = (1,2,5)→(1,3,6)"
  analyzeN4_L n4_l1 link1.1 link1.2 x5

  let link2 := ({ i := 3, j := 4, k := 5 }, { i := 3, j := 4, k := 6 })
  let n4_l2 := buildN4_L n4 link2.1 x5
  printNetwork n4_l2 s!"N₄(L) for L = (3,4,5)→(3,4,6)"
  analyzeN4_L n4_l2 link2.1 link2.2 x5

  -- Build and show F₅ (with example rigid pedigrees)
  let r4 : List RigidPedigree := []  -- Assume no rigid pedigrees for now

  let link_caps : List ((Node × Node) × Rat) := [
    (({ i := 1, j := 2, k := 5 }, { i := 1, j := 3, k := 6 }), 1/2),
    (({ i := 1, j := 2, k := 5 }, { i := 2, j := 3, k := 6 }), 1/2),
    (({ i := 3, j := 4, k := 5 }, { i := 3, j := 4, k := 6 }), 0)  -- Example: blocked
  ]

  let f5 := buildF5Network x5 x6 r4 link_caps
  printNetwork f5 "F₅ Bipartite Network"
  analyzeF5 f5 r4

  IO.println s!"\n{String.mk (List.replicate 60 '=')}"
  IO.println "Visualization Complete"
  IO.println s!"{String.mk (List.replicate 60 '=')}"

-- Uncomment to run when testing
-- #eval testData

end F5Visualization
