-- GraphInterface.lean
-- Lean4 Interface for NetworkX Graph Algorithms via subprocess
-- Supports: Max-Flow, SCC, Bipartite Matching, and Frozen Flow Detection
--
-- Requirements:
-- - Python 3 with NetworkX installed
-- - Python scripts: networkx_maxflow.py, networkx_scc.py,
--   networkx_matching.py, networkx_frozen.py

import Lean
import Lean.Data.Json
--deriving instance Lean.FromJson for Rat

-- Then you can use the notation

set_option maxHeartbeats 400000

namespace GraphInterface

-- ============================================================================
-- Data Structures
-- ============================================================================

/-- Edge representation with capacity and flow -/
structure Edge where
  «from» : Nat
  «to» : Nat
  capacity : Int
  flow : Int := 0
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- Bipartite graph structure -/
structure BipartiteGraph where
  leftSize : Nat
  rightSize : Nat
  edges : Array Edge
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- Flow network with source and sink -/
structure FlowNetwork where
  numVertices : Nat
  edges : Array Edge
  source : Nat
  sink : Nat
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- Result from max-flow computation -/
structure MaxFlowResult where
  maxFlowValueInt : Int  -- Receive as integer from Python
  flowEdges : Array (Nat × Nat × Int)
  deriving Repr, Lean.FromJson

/-- Convert integer max-flow value to Rat -/
def MaxFlowResult.maxFlowValue (r : MaxFlowResult) : Rat :=
  Rat.ofInt r.maxFlowValueInt
/-- Result from SCC computation -/
structure SCCResult where
  components : Array (Array Nat)
  numComponents : Nat
  componentMap : Array (Nat × Nat)  -- (vertex, componentId)
  deriving Repr, Lean.FromJson

/-- Result from bipartite matching -/
structure MatchingResult where
  matching : Array (Nat × Nat)
  matchingSize : Nat
  deriving Repr, Lean.FromJson

/-- Result from frozen flows computation -/
structure FrozenFlowsResult where
  frozenArcs : Array (Nat × Nat)
  interfaces : Array (Nat × Nat)
  bridges : Array (Nat × Nat)
  sccs : Array (Array Nat)
  deriving Repr, Lean.FromJson

-- ============================================================================
-- Python Interface via Subprocess
-- ============================================================================

/-- Call Python script with JSON input and return JSON output -/
def callPython (scriptPath : String) (inputJson : String) : IO String := do
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #[scriptPath]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }

  let (stdin, child) ← child.takeStdin
  stdin.putStr inputJson
  stdin.flush

  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  let output ← IO.ofExcept stdout.get

  if exitCode != 0 then
    IO.eprintln s!"Python error: {stderr}"
    throw <| IO.userError s!"Python script failed with code {exitCode}"

  return output.trimAscii.toString

-- ============================================================================
-- Graph Conversions
-- ============================================================================

/-- Convert bipartite graph to flow network with source and sink -/
def bipartiteToFlowNetwork (bg : BipartiteGraph) : FlowNetwork :=
  let totalVertices := bg.leftSize + bg.rightSize + 2
  let source : Nat := 0
  let sink : Nat := totalVertices - 1

  -- Add edges from source to left partition
  let sourceEdges : Array Edge := Array.range bg.leftSize |>.map fun i =>
    { «from» := source, «to» := i + 1, capacity := 1, flow := 0 : Edge }

  -- Shift original edges (left: 1..leftSize, right: leftSize+1..leftSize+rightSize)
  let shiftedEdges : Array Edge := bg.edges.map fun e =>
    { e with
      «from» := e.«from» + 1,
      «to» := e.«to» + bg.leftSize + 1 }

  -- Add edges from right partition to sink
  let sinkEdges : Array Edge := Array.range bg.rightSize |>.map fun i =>
    { «from» := bg.leftSize + i + 1, «to» := sink, capacity := 1, flow := 0 : Edge }

  { numVertices := totalVertices
  , edges := sourceEdges ++ shiftedEdges ++ sinkEdges
  , source := source
  , sink := sink }

/-- Compute residual graph edges from flow network and flow result -/
def computeResidualEdges (fn : FlowNetwork) (flowResult : MaxFlowResult) : Array Edge :=
  fn.edges.foldl (init := #[]) fun acc edge =>
    let flowValue : Int := flowResult.flowEdges.find?
      (fun (u, v, _) => u == edge.«from» && v == edge.«to»)
      |>.map (fun (_, _, fl) => fl) |>.getD 0

    -- Forward edge: remaining capacity
    let forward : Array Edge := if edge.capacity - flowValue > 0 then
      #[{ «from» := edge.«from», «to» := edge.«to»,
          capacity := edge.capacity - flowValue, flow := 0 : Edge }]
    else #[]

    -- Backward edge: current flow (can push back)
    let backward : Array Edge := if flowValue > 0 then
      #[{ «from» := edge.«to», «to» := edge.«from»,
          capacity := flowValue, flow := 0 : Edge }]
    else #[]

    acc ++ forward ++ backward

-- ============================================================================
-- Core Algorithm Functions
-- ============================================================================

/-- Compute maximum flow using NetworkX -/
def computeMaxFlow (fn : FlowNetwork)
    (scriptPath : String := "PedigreeProject/Algorithms/networkx_maxflow.py") : IO MaxFlowResult := do
  let json := Lean.toJson fn
  let output ← callPython scriptPath (toString json)

  match Lean.Json.parse output with
  | .ok json =>
    match Lean.fromJson? json with
    | .ok result => return result
    | .error e => throw <| IO.userError s!"JSON decode error: {e}"
  | .error e => throw <| IO.userError s!"JSON parse error: {e}"

/-- Compute strongly connected components using NetworkX -/
def computeSCCs (edges : Array Edge) (numVertices : Nat)
    (scriptPath : String := "PedigreeProject/Algorithms/networkx_scc.py") : IO SCCResult := do
  let input := Lean.toJson (edges, numVertices)
  let output ← callPython scriptPath (toString input)

  match Lean.Json.parse output with
  | .ok json =>
    match Lean.fromJson? json with
    | .ok result => return result
    | .error e => throw <| IO.userError s!"JSON decode error: {e}"
  | .error e => throw <| IO.userError s!"JSON parse error: {e}"

/-- Compute bipartite matching using NetworkX -/
def computeBipartiteMatching (bg : BipartiteGraph)
    (scriptPath : String := "PedigreeProject/Algorithms/networkx_matching.py") : IO MatchingResult := do
  let json := Lean.toJson bg
  let output ← callPython scriptPath (toString json)

  match Lean.Json.parse output with
  | .ok json =>
    match Lean.fromJson? json with
    | .ok result => return result
    | .error e => throw <| IO.userError s!"JSON decode error: {e}"
  | .error e => throw <| IO.userError s!"JSON parse error: {e}"

/-- Compute frozen flows (interfaces ∪ bridges) using NetworkX -/
def computeFrozenFlows (fn : FlowNetwork) (flowResult : MaxFlowResult)
    (scriptPath : String := "PedigreeProject/Algorithms/networkx_frozen.py") : IO FrozenFlowsResult := do
  let residualEdges : Array Edge := computeResidualEdges fn flowResult
  let input := Lean.toJson (residualEdges, fn.numVertices, fn.edges, flowResult.flowEdges)
  let output ← callPython scriptPath (toString input)

  match Lean.Json.parse output with
  | .ok json =>
    match Lean.fromJson? json with
    | .ok result => return result
    | .error e => throw <| IO.userError s!"JSON decode error: {e}"
  | .error e => throw <| IO.userError s!"JSON parse error: {e}"

-- ============================================================================
-- High-Level API Functions
-- ============================================================================

/-- Compute max-flow for a bipartite graph -/
def computeBipartiteMaxFlow (bg : BipartiteGraph) : IO MaxFlowResult := do
  let fn : FlowNetwork := bipartiteToFlowNetwork bg
  computeMaxFlow fn

/-- Compute SCCs in residual graph after max-flow -/
def computeResidualSCCs (bg : BipartiteGraph) : IO SCCResult := do
  let fn : FlowNetwork := bipartiteToFlowNetwork bg
  let flowResult ← computeMaxFlow fn
  let residualEdges : Array Edge := computeResidualEdges fn flowResult
  computeSCCs residualEdges fn.numVertices

/-- Compute frozen flows for a bipartite graph -/
def computeBipartiteFrozenFlows (bg : BipartiteGraph) : IO FrozenFlowsResult := do
  let fn : FlowNetwork := bipartiteToFlowNetwork bg
  let flowResult ← computeMaxFlow fn
  computeFrozenFlows fn flowResult

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Check if an arc is frozen -/
def isArcFrozen (frozenResult : FrozenFlowsResult) (u v : Nat) : Bool :=
  frozenResult.frozenArcs.any fun (src, dst) => src == u && dst == v

/-- Get all frozen arcs with their flow values -/
def getFrozenArcsWithFlows (frozenResult : FrozenFlowsResult)
    (flowResult : MaxFlowResult) : Array (Nat × Nat × Int) :=
  frozenResult.frozenArcs.filterMap fun (u, v) =>
    flowResult.flowEdges.find? fun (src, dst, _) => src == u && dst == v

/-- Get number of interfaces (arcs between SCCs) -/
def numInterfaces (frozenResult : FrozenFlowsResult) : Nat :=
  frozenResult.interfaces.size

/-- Get number of bridges (bridge arcs within SCCs) -/
def numBridges (frozenResult : FrozenFlowsResult) : Nat :=
  frozenResult.bridges.size

/-- Check if solution is unique (all arcs frozen) -/
def hasUniqueSolution (frozenResult : FrozenFlowsResult) (flowResult : MaxFlowResult) : Bool :=
  frozenResult.frozenArcs.size == flowResult.flowEdges.size

/-- Check if solution has maximum flexibility (no frozen arcs) -/
def hasMaximumFlexibility (frozenResult : FrozenFlowsResult) : Bool :=
  frozenResult.frozenArcs.size == 0

-- ============================================================================
-- Example Graphs
-- ============================================================================

/-- Example: Simple bipartite graph -/
def exampleSimpleGraph : BipartiteGraph :=
  { leftSize := 3
  , rightSize := 3
  , edges := #[
      { «from» := 0, «to» := 0, capacity := 1 },
      { «from» := 0, «to» := 1, capacity := 1 },
      { «from» := 1, «to» := 1, capacity := 1 },
      { «from» := 1, «to» := 2, capacity := 1 },
      { «from» := 2, «to» := 0, capacity := 1 },
      { «from» := 2, «to» := 2, capacity := 1 }
    ]
  }

/-- Example: Complete bipartite K₃,₃ (no frozen arcs) -/
def exampleCompleteGraph : BipartiteGraph :=
  { leftSize := 3
  , rightSize := 3
  , edges := #[
      { «from» := 0, «to» := 0, capacity := 1 },
      { «from» := 0, «to» := 1, capacity := 1 },
      { «from» := 0, «to» := 2, capacity := 1 },
      { «from» := 1, «to» := 0, capacity := 1 },
      { «from» := 1, «to» := 1, capacity := 1 },
      { «from» := 1, «to» := 2, capacity := 1 },
      { «from» := 2, «to» := 0, capacity := 1 },
      { «from» := 2, «to» := 1, capacity := 1 },
      { «from» := 2, «to» := 2, capacity := 1 }
    ]
  }

/-- Example: Graph with bottlenecks (some frozen arcs) -/
def exampleBottleneckGraph : BipartiteGraph :=
  { leftSize := 4
  , rightSize := 4
  , edges := #[
      { «from» := 0, «to» := 0, capacity := 1 },  -- Forced
      { «from» := 1, «to» := 1, capacity := 1 },  -- Flexible
      { «from» := 1, «to» := 2, capacity := 1 },
      { «from» := 2, «to» := 1, capacity := 1 },  -- Flexible
      { «from» := 2, «to» := 2, capacity := 1 },
      { «from» := 3, «to» := 3, capacity := 1 }   -- Forced
    ]
  }

/-- Example: Unique matching (all frozen arcs) -/
def exampleUniqueGraph : BipartiteGraph :=
  { leftSize := 4
  , rightSize := 4
  , edges := #[
      { «from» := 0, «to» := 0, capacity := 1 },
      { «from» := 1, «to» := 1, capacity := 1 },
      { «from» := 2, «to» := 2, capacity := 1 },
      { «from» := 3, «to» := 3, capacity := 1 }
    ]
  }

end GraphInterface
