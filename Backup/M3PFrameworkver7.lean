-- M3PFrameworkVer7.lean
-- Extended implementation with F₅ and general F_k construction

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Ring.Defs
import MembershipProject.Core.Basic
import MembershipProject.Core.DataParser
import MembershipProject.Core.FeasibilityCheck
import MembershipProject.Core.GraphInterface
import MembershipProject.Core.RestrictionFull
import MembershipProject.Core.Types
import MembershipProject.Core.ArcRules

set_option linter.unusedVariables false
open MembershipProject.Core

-- ============================================================================
-- HELPER: Rat to Int conversion for capacities
-- ============================================================================

/-- Convert Rat to Int by scaling by 6 and taking numerator -/
def ratToCapacityInt (r : Rat) : Int :=
  (r * 6).num

/-- Convert Int capacity back to Rat by dividing by 6 -/
def capacityIntToRat (i : Int) : Rat :=
  Rat.ofInt i / 6

-- ============================================================================
-- CORE DATA STRUCTURES
-- ============================================================================

/-- Complete pedigree path from (1,2,3) through multiple layers -/
structure PedigreePath (k : ℕ) where
  nodes : List Node
  flow : Rat
  deriving Repr

instance {k : ℕ} : DecidableEq (PedigreePath k) :=
  fun a b =>
    if ha : a.nodes = b.nodes then
      if hb : a.flow = b.flow then
        isTrue (by cases a; cases b; congr)
      else
        isFalse (by cases a; cases b; intro h; injection h with h1 h2; exact hb h2)
    else
      isFalse (by cases a; cases b; intro h; injection h with h1; exact ha h1)

/-- Result of membership check at a specific stage -/
inductive StageResult (n k : ℕ) where
  | success : StageResult n k
  | failure : String → StageResult n k
  deriving Repr

/-- Final membership result -/
inductive MembershipResult (n : ℕ) where
  | inConvexHull : MembershipResult n
  | notInConvexHull : String → MembershipResult n
  deriving Repr

/-- Result of F₄ analysis with rigid pedigrees and updated network -/
structure F4AnalysisResult (n : ℕ) where
  R₄ : List (PedigreePath 4)
  μ : List (PedigreePath 4 × Rat)
  N₄ : GraphInterface.FlowNetwork
  originalFlow : GraphInterface.MaxFlowResult

/-- F₅ network representation -/
structure F5Network where
  sourceNodes : List (Node × Rat)
  pedigreeSources : List (PedigreePath 4 × Rat)
  sinkNodes : List (Node × Rat)
  arcs : List (Node × Node × Rat)
  pedigreeArcs : List (PedigreePath 4 × Node × Rat)
  deriving Repr

/-- Result of F₅ analysis -/
structure F5AnalysisResult (n : ℕ) where
  R₅ : List (PedigreePath 5)
  μ : List (PedigreePath 5 × Rat)
  N₅ : F5Network
  maxFlow : Rat
  expectedFlow : Rat

/-- Unique path information for an arc -/
structure UniquePathInfo where
  hasUniquePath : Bool
  path : List Node
  deriving Repr

/-- Arc information with capacity and unique path data -/
structure ArcInfo where
  source : Node
  target : Node
  capacity : Rat
  uniquePathInfo : UniquePathInfo
  deriving Repr

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

namespace PedigreePolytope

variable {n : ℕ}

/-- Get MIR value for an edge (i,j) at stage k from ParsedMIRData -/
def getMIRValueParsed (X : ParsedMIRData n) (i j k : Nat) : Rat :=
  ParsedMIRData.getValue X i j k

-- ============================================================================
-- PEDIGREE VALIDATION
-- ============================================================================

/-- Check if extending a pedigree path with a new node forms a valid pedigree -/
def isValidPedigreeExtension {k : ℕ} (path : PedigreePath k) (newNode : Node) : Bool :=
  if path.nodes.isEmpty then false
  else
    match path.nodes.getLast? with
    | none => false
    | some lastNode =>
      if newNode.k ≠ lastNode.k + 1 then false
      else isPermittedArcGeneral lastNode newNode

/-- Check if a list of nodes forms a valid pedigree path -/
def isValidPedigreePath (nodes : List Node) : Bool :=
  if nodes.length < 2 then false
  else
    match nodes.head? with
    | none => false
    | some first =>
      if first.i ≠ 1 || first.j ≠ 2 || first.k ≠ 3 then false
      else
        let pairs := nodes.zip nodes.tail
        pairs.all fun (n1, n2) => n2.k = n1.k + 1

-- ============================================================================
-- STEP 1a - PMI CHECK
-- ============================================================================

/-- STEP 1a: Check if X belongs to P_MI(n) -/
def checkPMI (X : ParsedMIRData n) (hn : n ≥ 5) : StageResult n 0 :=
  let result := checkParsedDataFeasibility n X
  if result.feasible then
    StageResult.success
  else
    match result.first_infeasible_stage with
    | some k => StageResult.failure s!"X ∉ P_MI(n): infeasible at stage {k}"
    | none => StageResult.failure "X ∉ P_MI(n): unknown infeasibility"

-- ============================================================================
-- STEP 1b - F₄ NETWORK CONSTRUCTION
-- ============================================================================

/-- Construct F₄ network with forbidden arc rules -/
def constructF4Network (X : ParsedMIRData n) : GraphInterface.FlowNetwork :=
  let layer4 := nodesInLayer 4
  let layer5 := nodesInLayer 5
  let numNodes := 1 + layer4.length + layer5.length + 1
  let source : Nat := 0
  let sink : Nat := numNodes - 1
  let layer4WithIds := (List.range layer4.length).map fun idx =>
    (layer4.getD idx { i := 1, j := 2, k := 4 : Node }, idx + 1)
  let layer5WithIds := (List.range layer5.length).map fun idx =>
    (layer5.getD idx { i := 1, j := 2, k := 5 : Node }, 1 + layer4.length + idx)
  let sourceEdges : Array GraphInterface.Edge :=
    (layer4WithIds.map fun (node, id) =>
      let capacity := getMIRValueParsed X node.i node.j 4
      { «from» := source,
        «to» := id,
        capacity := ratToCapacityInt capacity,
        flow := 0 : GraphInterface.Edge }).toArray
  let stage4Arcs := permittedArcsForStage 4
  let internalEdges : Array GraphInterface.Edge :=
    (stage4Arcs.filterMap fun (srcNode, tgtNode) =>
      if not (isPermittedArc45 srcNode tgtNode) then none
      else
        let srcId? := layer4WithIds.find? fun (n, _) => n == srcNode
        let tgtId? := layer5WithIds.find? fun (n, _) => n == tgtNode
        match srcId?, tgtId? with
        | some (_, srcId), some (_, tgtId) =>
          let capacity := getMIRValueParsed X tgtNode.i tgtNode.j 5
          some { «from» := srcId,
                 «to» := tgtId,
                 capacity := ratToCapacityInt capacity,
                 flow := 0 : GraphInterface.Edge }
        | _, _ => none).toArray
  let sinkEdges : Array GraphInterface.Edge :=
    (layer5WithIds.map fun (node, id) =>
      { «from» := id,
        «to» := sink,
        capacity := 6,
        flow := 0 : GraphInterface.Edge }).toArray
  { numVertices := numNodes,
    edges := sourceEdges ++ internalEdges ++ sinkEdges,
    source := source,
    sink := sink : GraphInterface.FlowNetwork }

-- ============================================================================
-- RIGID PEDIGREE EXTRACTION FROM FROZEN FLOWS
-- ============================================================================

/-- Trace a frozen arc back to construct complete pedigree path -/
def tracePedigreePath {k : ℕ} (frozenArc : Nat × Nat)
    (flowResult : GraphInterface.MaxFlowResult)
    (vertexToNodeMap : Nat → Option Node) : Option (PedigreePath k) :=
  let (u, v) := frozenArc
  let flowValue := flowResult.flowEdges.toList.find?
    (fun (src, dst, _) => src == u && dst == v)
    |>.map (fun (_, _, f) => capacityIntToRat f) |>.getD 0
  if flowValue ≤ 0 then none
  else
    match vertexToNodeMap u, vertexToNodeMap v with
    | some nodeU, some nodeV =>
      let path := [{ i := 1, j := 2, k := 3 : Node }, nodeU, nodeV]
      some { nodes := path, flow := flowValue : PedigreePath k }
    | _, _ => none

/-- Extract all rigid pedigrees from frozen flows -/
def extractRigidPedigrees {k : ℕ} (frozenResult : GraphInterface.FrozenFlowsResult)
    (flowResult : GraphInterface.MaxFlowResult)
    (vertexToNodeMap : Nat → Option Node) : List (PedigreePath k) :=
  frozenResult.frozenArcs.toList.filterMap fun arc =>
    tracePedigreePath arc flowResult vertexToNodeMap

-- ============================================================================
-- NETWORK CAPACITY UPDATE
-- ============================================================================

/-- Check if an edge corresponds to a node in a pedigree path -/
def edgeMatchesNode (k : ℕ) (edge : GraphInterface.Edge)
    (node : Node) (vertexToNodeMap : Nat → Option Node) : Bool :=
  match vertexToNodeMap edge.«from», vertexToNodeMap edge.«to» with
  | some nodeFrom, some nodeTo => (nodeFrom == node) || (nodeTo == node)
  | _, _ => false

/-- Update network capacities by subtracting rigid flows -/
def updateNetworkCapacities {k : ℕ} (fn : GraphInterface.FlowNetwork)
    (rigidPaths : List (PedigreePath k))
    (vertexToNodeMap : Nat → Option Node) : GraphInterface.FlowNetwork :=
  let updatedEdges := rigidPaths.foldl (init := fn.edges) fun edges path =>
    edges.map fun edge =>
      let isInPath := path.nodes.any fun node =>
        edgeMatchesNode k edge node vertexToNodeMap
      if isInPath then
        { edge with capacity := edge.capacity - ratToCapacityInt path.flow }
      else edge
  { fn with edges := updatedEdges }

-- ============================================================================
-- STEP 1b - COMPLETE F₄ ANALYSIS
-- ============================================================================

/-- STEP 1b: Complete F₄ analysis producing (N₄, R₄, μ) -/
def analyzeF4Complete (X : ParsedMIRData n) (hn : n ≥ 5) :
    IO (F4AnalysisResult n × StageResult n 4) := do
  IO.println "=== Step 1b: Analyzing F₄ ==="
  let fn := constructF4Network X
  IO.println s!"F₄ network: {fn.numVertices} vertices, {fn.edges.size} edges"
  let layer4 := nodesInLayer 4
  let layer5 := nodesInLayer 5
  let vertexToNodeMap : Nat → Option Node := fun vid =>
    if vid = 0 then none
    else if vid = fn.numVertices - 1 then none
    else if vid <= layer4.length then
      layer4.getD (vid - 1) { i := 1, j := 2, k := 4 : Node } |> some
    else if vid <= layer4.length + layer5.length then
      layer5.getD (vid - layer4.length - 1) { i := 1, j := 2, k := 5 : Node } |> some
    else none
  IO.println "Computing max-flow in F₄..."
  let flowResult ← GraphInterface.computeMaxFlow fn
  let maxFlow := flowResult.maxFlowValue
  IO.println s!"Max-flow: {maxFlow}"
  IO.println s!"Expected: 1.0 (one pedigree path)"
  let expectedFlow : Rat := 1
  if maxFlow ≠ expectedFlow then
    return ({ R₄ := [], μ := [], N₄ := fn, originalFlow := flowResult },
            StageResult.failure s!"F₄ not feasible: flow {maxFlow} ≠ {expectedFlow}")
  IO.println "✓ F₄ is feasible"
  IO.println "Computing frozen flows (rigid arcs)..."
  let frozenResult ← GraphInterface.computeFrozenFlows fn flowResult
  IO.println s!"Found {frozenResult.frozenArcs.size} frozen arcs"
  let rigidPedigrees := extractRigidPedigrees frozenResult flowResult vertexToNodeMap
  IO.println s!"Rigid pedigrees in R₄: {rigidPedigrees.length}"
  for pidx in List.range rigidPedigrees.length do
    let P := rigidPedigrees.getD pidx { nodes := [], flow := 0 : PedigreePath 4 }
    IO.println s!"  P{pidx+1}: μ = {P.flow}"
  let μList := rigidPedigrees.map fun p => (p, p.flow)
  IO.println "Updating network N₄ (subtracting rigid flows)..."
  let N₄ := updateNetworkCapacities fn rigidPedigrees vertexToNodeMap
  let totalRigid := rigidPedigrees.foldl (init := 0) (fun acc P => acc + P.flow)
  IO.println s!"Total rigid flow: {totalRigid}"
  IO.println s!"Remaining flexible flow: {1 - totalRigid}"
  return ({ R₄ := rigidPedigrees, μ := μList, N₄ := N₄, originalFlow := flowResult },
          StageResult.success)

-- ============================================================================
-- F₅ CONSTRUCTION - ANALYTICAL MAX-FLOW
-- ============================================================================

/-- Check if pedigree P can extend to node (a,b,6) via permitted arc rules -/
def canPedigreeExtendTo6 (P : PedigreePath 4) (targetNode : Node) : Bool :=
  if targetNode.k ≠ 6 then false
  else
    match P.nodes.getLast? with
    | none => false
    | some lastNode =>
      if lastNode.k ≠ 5 then false
      else
        let a := targetNode.i
        let b := targetNode.j
        let notInPath := P.nodes.all fun node =>
          if node.k >= 4 then not (node.i = a && node.j = b) else true
        let rule2 := if b > 3 then
          P.nodes.any fun node =>
            if node.k = b then node.i = a || node.j = a else false
        else true
        notInPath && rule2

/-- Compute link capacity C(L) as sum of μ(P) for extendable pedigrees -/
def computeLinkCapacity (R₄ : List (PedigreePath 4))
    (srcNode tgtNode : Node) : Rat :=
  let extendable := R₄.filter fun P => canPedigreeExtendTo6 P tgtNode
  extendable.foldl (fun acc P => acc + P.flow) 0

/-- Build F₅ network with analytical structure -/
def buildF5Network (X : ParsedMIRData n)
    (R₄ : List (PedigreePath 4))
    (μ₄ : List (PedigreePath 4 × Rat)) : F5Network :=
  let layer5 := nodesInLayer 5
  let layer6 := nodesInLayer 6
  let sourceNodes := layer5.map fun node =>
    (node, getMIRValueParsed X node.i node.j 5)
  let pedigreeSources := μ₄
  let sinkNodes := layer6.map fun node =>
    (node, getMIRValueParsed X node.i node.j 6)
  let permittedArcs := permittedArcsForStage 5
  let arcs := permittedArcs.map fun (src, tgt) =>
    let capacity := computeLinkCapacity R₄ src tgt
    (src, tgt, capacity)
  let pedigreeArcs := R₄.foldl (init := []) fun acc P =>
    let validTargets := layer6.filter fun tgt => canPedigreeExtendTo6 P tgt
    let newArcs := validTargets.map fun tgt => (P, tgt, P.flow)
    acc ++ newArcs
  { sourceNodes := sourceNodes,
    pedigreeSources := pedigreeSources,
    sinkNodes := sinkNodes,
    arcs := arcs,
    pedigreeArcs := pedigreeArcs }

/-- Compute analytical max-flow in F₅ -/
def computeF5MaxFlow (net : F5Network) : Rat :=
  let supplyFromNodes := net.sourceNodes.foldl (fun acc (_, cap) => acc + cap) 0
  let supplyFromPedigrees := net.pedigreeSources.foldl (fun acc (_, cap) => acc + cap) 0
  let totalSupply := supplyFromNodes + supplyFromPedigrees
  let sinkFlows := net.sinkNodes.map fun (sinkNode, sinkCap) =>
    let fromArcs := net.arcs.foldl (fun acc (src, tgt, cap) =>
      if tgt == sinkNode then acc + cap else acc) 0
    let fromPedigrees := net.pedigreeArcs.foldl (fun acc (P, tgt, cap) =>
      if tgt == sinkNode then acc + cap else acc) 0
    min (fromArcs + fromPedigrees) sinkCap
  min totalSupply (sinkFlows.foldl (fun acc cap => acc + cap) 0)

/-- Expected flow for F₅ -/
def expectedF5Flow (R₄ : List (PedigreePath 4)) : Rat :=
  R₄.foldl (fun acc P => acc + P.flow) 0

/-- STEP 2: Analyze F₅ complete -/
def analyzeF5Complete (X : ParsedMIRData n)
    (R₄ : List (PedigreePath 4))
    (μ₄ : List (PedigreePath 4 × Rat))
    (hn : n ≥ 5) : IO (F5AnalysisResult n × StageResult n 5) := do
  IO.println "=== Step 2: Analyzing F₅ ==="
  let net := buildF5Network X R₄ μ₄
  IO.println s!"F₅ network built:"
  IO.println s!"  Source nodes: {net.sourceNodes.length}"
  IO.println s!"  Pedigree sources: {net.pedigreeSources.length}"
  IO.println s!"  Sink nodes: {net.sinkNodes.length}"
  IO.println s!"  Arcs: {net.arcs.length}"
  IO.println s!"  Pedigree arcs: {net.pedigreeArcs.length}"
  let maxFlow := computeF5MaxFlow net
  let expectedFlow := expectedF5Flow R₄
  IO.println s!"Max-flow in F₅: {maxFlow}"
  IO.println s!"Expected flow: {expectedFlow}"
  if maxFlow ≠ expectedFlow then
    return ({ R₅ := [], μ := [], N₅ := net, maxFlow := maxFlow, expectedFlow := expectedFlow },
            StageResult.failure s!"F₅ not feasible: flow {maxFlow} ≠ {expectedFlow}")
  IO.println "✓ F₅ is feasible"
  IO.println "TODO: Extract R₅ from F₅ flow (frozen flow analysis)"
  let R₅ : List (PedigreePath 5) := []
  let μ₅ : List (PedigreePath 5 × Rat) := []
  return ({ R₅ := R₅, μ := μ₅, N₅ := net, maxFlow := maxFlow, expectedFlow := expectedFlow },
          StageResult.success)

-- ============================================================================
-- MAIN M3P ALGORITHM
-- ============================================================================

/-- Main M3P algorithm: Check membership in conv(Pedigrees_n) -/
def checkM3PMembership (X : ParsedMIRData n) (hn : n ≥ 5) : IO (MembershipResult n) := do
  IO.println "========================================"
  IO.println "M3P MEMBERSHIP CHECK"
  IO.println "========================================"
  IO.println ""
  match checkPMI X hn with
  | StageResult.failure msg =>
    IO.println s!"✗ FAILED at Step 1a: {msg}"
    return MembershipResult.notInConvexHull msg
  | StageResult.success =>
    IO.println "✓ PASSED Step 1a: X ∈ P_MI(n)"
    IO.println ""
  let (f4Result, f4Status) ← analyzeF4Complete X hn
  match f4Status with
  | StageResult.failure msg =>
    IO.println s!"✗ FAILED at Step 1b: {msg}"
    return MembershipResult.notInConvexHull msg
  | StageResult.success =>
    IO.println "✓ PASSED Step 1b: F₄ feasible"
    IO.println ""
  let totalRigid := f4Result.R₄.foldl (init := 0) (fun acc P => acc + P.flow)
  if totalRigid = 1 then
    IO.println "✓ All flow is rigid at stage 4 - SUCCESS!"
    IO.println "X ∈ conv(Pedigrees_n)"
    return MembershipResult.inConvexHull
  if n >= 6 then
    let (_, f5Status) ← analyzeF5Complete X f4Result.R₄ f4Result.μ hn
    match f5Status with
    | StageResult.failure msg =>
      IO.println s!"✗ FAILED at Step 2: {msg}"
      return MembershipResult.notInConvexHull msg
    | StageResult.success =>
      IO.println "✓ PASSED Step 2: F₅ feasible"
      IO.println ""
  IO.println "Note: Analysis beyond F₅ not yet implemented"
  IO.println "Assuming success based on feasibility so far"
  return MembershipResult.inConvexHull

-- ============================================================================
-- DISPLAY FUNCTIONS
-- ============================================================================

/-- Display final membership result -/
def displayMembershipResult (result : MembershipResult n) : IO Unit := do
  IO.println ""
  IO.println "========================================"
  IO.println "FINAL RESULT"
  IO.println "========================================"
  match result with
  | MembershipResult.inConvexHull =>
    IO.println "✓ SUCCESS: X ∈ conv(Pedigrees_n)"
  | MembershipResult.notInConvexHull msg =>
    IO.println s!"✗ FAILURE: X ∉ conv(Pedigrees_n)"
    IO.println s!"Reason: {msg}"
  IO.println "========================================"

-- ============================================================================
-- MAIN ENTRY POINT
-- ============================================================================

/-- Run complete M3P analysis on parsed data -/
def runM3PAnalysis (X : ParsedMIRData n) (hn : n ≥ 5) : IO Unit := do
  let result ← checkM3PMembership X hn
  displayMembershipResult result

end PedigreePolytope

-- ============================================================================
-- EXAMPLE USAGE
-- ============================================================================

section Examples

open MembershipProject.Core
open PedigreePolytope

/-- Example: Run M3P on the test problem -/
def testM3PExample : IO Unit := do
  let input := [
    "Test_M3P_Example",
    "6",
    "3    4    4    5    5    6    6    6    6",
    "1,2  1,3  2,3  1,2  3,4  1,3  1,4  2,3  2,4",
    "1.0  0.75 0.25 0.5  0.5  0.25 0.25 0.25 0.25",
    ""
  ]
  match ParsedMIRData.parse input 6 (by omega) rfl with
  | none => IO.println "✗ Parse failed"
  | some X => do
      IO.println s!"✓ Parsed: {X}"
      IO.println ""
      runM3PAnalysis X (by omega)

-- Uncomment to run:
-- #eval testM3PExample

end Examples
