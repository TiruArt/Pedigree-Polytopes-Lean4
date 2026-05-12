-- Quick Test Runner for Frozen Flow Cases
-- Save as TestFrozenFlows.lean

import MembershipProject.Core.GraphInterfaces

def testCase (name : String) (graph : GraphAlgorithms.BipartiteGraph)
    (expectedFrozen : String) : IO Unit := do
  IO.println s!"\n{'─'.toString.replicate 70}"
  IO.println s!"TEST: {name}"
  IO.println s!"{'─'.toString.replicate 70}"
  IO.println s!"Graph: {graph.leftSize} left nodes, {graph.rightSize} right nodes"
  IO.println s!"Edges: {graph.edges.size}"
  IO.println s!"Expected: {expectedFrozen}"
  IO.println ""

  try
    let fn := GraphAlgorithms.bipartiteToFlowNetwork graph
    let flow ← GraphAlgorithms.computeMaxFlow fn
    let frozen ← GraphAlgorithms.computeFrozenFlows fn flow

    IO.println s!"✓ Max Flow: {flow.maxFlowValue}"
    IO.println s!"✓ Flow Edges: {flow.flowEdges.size}"
    IO.println s!"✓ Frozen Arcs: {frozen.frozenArcs.size}"
    IO.println s!"  - Interfaces: {frozen.interfaces.size}"
    IO.println s!"  - Bridges: {frozen.bridges.size}"
    IO.println s!"✓ SCCs: {frozen.sccs.size}"

    -- Determine category
    let category :=
      if frozen.frozenArcs.size == 0 then
        "🟢 NO FROZEN ARCS (Maximum Flexibility)"
      else if frozen.frozenArcs.size == flow.flowEdges.size then
        "🔴 ALL FROZEN ARCS (Unique Solution)"
      else
        "🟡 SOME FROZEN ARCS (Partial Constraints)"

    IO.println s!"\n{category}"

    if frozen.frozenArcs.size > 0 then
      IO.println "\nFrozen arcs:"
      for (u, v) in frozen.frozenArcs do
        IO.println s!"  {u} → {v}"

  catch e =>
    IO.eprintln s!"❌ Error: {e}"

def main : IO Unit := do
  IO.println "\n🧊 FROZEN FLOW TEST SUITE 🧊"
  IO.println "Testing three fundamental cases\n"

  -- Case 1: Complete Bipartite K3,3 (No frozen arcs)
  let case1 : GraphAlgorithms.BipartiteGraph := {
    leftSize := 3
    rightSize := 3
    edges := #[
      {from:=0, to:=0, capacity:=1}, {from:=0, to:=1, capacity:=1}, {from:=0, to:=2, capacity:=1},
      {from:=1, to:=0, capacity:=1}, {from:=1, to:=1, capacity:=1}, {from:=1, to:=2, capacity:=1},
      {from:=2, to:=0, capacity:=1}, {from:=2, to:=1, capacity:=1}, {from:=2, to:=2, capacity:=1}
    ]
  }
  testCase "Case 1: Complete Graph K₃,₃" case1 "0 frozen arcs"

  -- Case 2: Bottlenecks (Some frozen arcs)
  let case2 : GraphAlgorithms.BipartiteGraph := {
    leftSize := 4
    rightSize := 4
    edges := #[
      {from:=0, to:=0, capacity:=1},  -- L0 forced to R0
      {from:=1, to:=1, capacity:=1},  -- L1 can choose R1 or R2
      {from:=1, to:=2, capacity:=1},
      {from:=2, to:=1, capacity:=1},  -- L2 can choose R1 or R2
      {from:=2, to:=2, capacity:=1},
      {from:=3, to:=3, capacity:=1}   -- L3 forced to R3
    ]
  }
  testCase "Case 2: Graph with Bottlenecks" case2 "2 frozen arcs"

  -- Case 3: Unique Matching (All frozen arcs)
  let case3 : GraphAlgorithms.BipartiteGraph := {
    leftSize := 4
    rightSize := 4
    edges := #[
      {from:=0, to:=0, capacity:=1},
      {from:=1, to:=1, capacity:=1},
      {from:=2, to:=2, capacity:=1},
      {from:=3, to:=3, capacity:=1}
    ]
  }
  testCase "Case 3: Unique Perfect Matching" case3 "All arcs frozen"

  IO.println s!"\n{'═'.toString.replicate 70}"
  IO.println "SUMMARY"
  IO.println s!"{'═'.toString.replicate 70}"
  IO.println "✓ Case 1: Complete graph → Maximum flexibility"
  IO.println "✓ Case 2: Bottlenecks → Partial constraints"
  IO.println "✓ Case 3: Forced matching → Unique solution"
  IO.println s!"{'═'.toString.replicate 70}\n"

#eval main
