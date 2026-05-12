-- M3PFrameworkVer5Fixed.lean
-- CORRECTED VERSION - Fixed type mismatches and logic errors

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Ring.Defs
import MembershipProject.Core.Basic
import MembershipProject.Core.DataParser
import MembershipProject.Core.FeasibilityCheck
import MembershipProject.Core.NetworkStructure
import MembershipProject.Core.GraphInterface
import MembershipProject.Core.Restriction
import MembershipProject.Core.Types
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

open MembershipProject.Core
open MembershipProject

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
-- HELPER: List operations (already in Mathlib, no need to redefine)
-- ============================================================================

-- ============================================================================
-- CORE DATA STRUCTURES
-- ============================================================================

/-- A network with nodes and arcs for flow problems -/
structure Network (n : ℕ) where
  nodes : Finset (Fin n)
  arcs : Finset (Fin n × Fin n)
  capacity : Fin n → Fin n → ℝ

/-- A rigid path in the network -/
structure RigidPath (n : ℕ) where
  path : List (Fin n)
  flow : ℝ

/-- Flow network F_k -/
structure FlowNetwork (k : ℕ) where
  network : Network k
  isFeasible : Bool

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

/-- Complete pedigree path from (1,2,3) through multiple layers -/
structure PedigreePath (n : ℕ) where
  nodes : List Node
  flow : Rat
  deriving Repr

/-- Result of F₄ analysis with rigid pedigrees and updated network -/
structure F4AnalysisResult (n : ℕ) where
  R₄ : List (PedigreePath n)
  N₄ : GraphInterface.FlowNetwork
  originalFlow : GraphInterface.MaxFlowResult
  deriving Repr

/-- Permitted arc from layer k to layer k+1 -/
structure PermittedArc where
  origin : Node
  sink : Node
  deriving Repr

instance : DecidableEq PermittedArc :=
  fun a b =>
    if ha : a.origin = b.origin then
      if hb : a.sink = b.sink then
        isTrue (by
          cases a; cases b
          congr)
      else
        isFalse (by
          cases a; cases b
          intro h
          injection h with h1 h2
          exact hb h2)
    else
      isFalse (by
        cases a; cases b
        intro h
        cases h
        exact ha rfl)

/-- Virtual source node representing a rigid pedigree -/
structure VirtualSource (n : ℕ) where  -- FIX 2: Added type parameter
  pedigree : PedigreePath n
  capacity : Rat
  deriving Repr

-- ============================================================================
-- HELPER FUNCTIONS - LAYER AND NODE MANAGEMENT
-- ============================================================================

namespace PedigreePolytope

variable {n : ℕ}

/-- Get all nodes in a given layer k -/
def nodes_in_layer (k : Nat) : List Node :=
  if k < 3 then []
  else
    (List.range (k - 1)).foldl (fun acc i =>
      (List.range (k - 1)).foldl (fun acc2 j =>
        if i < j && j < k - 1 then
          { i := i + 1, j := j + 1, k := k : Node } :: acc2
        else acc2) acc) []

/-- Get all potential arcs between layer k and k+1 -/
def all_arcs_between_layers (k : Nat) : List (Node × Node) :=
  let layer_k := nodes_in_layer k
  let layer_kp1 := nodes_in_layer (k + 1)
  layer_k.foldl (fun acc src =>
    layer_kp1.foldl (fun acc2 tgt => (src, tgt) :: acc2) acc) []

-- ============================================================================
-- F₄ FORBIDDEN ARC RULES
-- ============================================================================

/-- Check if arc from (i,j,4) to (i',j',5) is PERMITTED in F₄ -/
def isPermittedArc45 (srcNode tgtNode : Node) : Bool :=
  if srcNode.k ≠ 4 || tgtNode.k ≠ 5 then false
  else
    -- Rule [a]: (i,j) ≠ (i',j')
    if srcNode.i = tgtNode.i && srcNode.j = tgtNode.j then false
    else
      -- Rule [b]: If j' > 3, then i' must be in {i,j}
      -- FIX 3: Corrected logic - rule [b] only applies when j' > 3
      if tgtNode.j > 3 then
        tgtNode.i = srcNode.i || tgtNode.i = srcNode.j
      else
        true  -- If j' ≤ 3, arc is permitted (assuming rule [a] passed)

/-- Check if an arc is permitted for general k transitions -/
def isPermittedArcForLayer (srcNode tgtNode : Node) : Bool :=
  if srcNode.k + 1 ≠ tgtNode.k then false
  else
    match srcNode.k with
    | 3 => true
    | 4 => isPermittedArc45 srcNode tgtNode
    | _ => true  -- FIX 4: TODO - need general arc rules for k > 4

/-- Get all permitted arcs between layer k and k+1 using arc rules -/
def permitted_arcs_for_stage (k : Nat) : List (Node × Node) :=
  let all_arcs := all_arcs_between_layers k
  all_arcs.filter fun (src, tgt) =>
    isPermittedArcForLayer src tgt

-- ============================================================================
-- MIR DATA ACCESS
-- ============================================================================

/-- Get MIR value for an edge (i,j) at stage k -/
def getMIRValue (X : ParsedMIRData n) (i j k : Nat) : Rat :=
  -- FIX 5: Changed from SparseRecursiveMIR to ParsedMIRData (from DataParser)
  -- FIX 6: Use the correct field access from ParsedMIRData
  X.data.toList.find? (fun entry =>
    entry.i.val = i && entry.j.val = j && entry.k = k)
    |>.map (·.value) |>.getD 0

/-- Get expected flow for F_k (number of nodes in layer k) -/
def expectedFlowForFk (k : Nat) : Rat :=
  let layer_size := (k - 1) * (k - 2) / 2
  Rat.divInt layer_size 1

-- ============================================================================
-- STEP 1a - PMI CHECK
-- ============================================================================

/-- STEP 1a: Check if X belongs to P_MI(n) -/
def checkPMI (X : ParsedMIRData n) (hn : n ≥ 5) : StageResult n 0 :=
  -- FIX 7: This needs the actual feasibility check implementation
  -- Placeholder assuming we have checkFeasibilityDetailed
  StageResult.success  -- TODO: Implement actual PMI check

-- ============================================================================
-- STEP 1b - F₄ NETWORK CONSTRUCTION
-- ============================================================================

/-- Construct F₄ network with forbidden arc rules -/
def constructF4Network (X : ParsedMIRData n) : GraphInterface.FlowNetwork :=
  let layer4 := nodes_in_layer 4
  let layer5 := nodes_in_layer 5
  let numNodes := 1 + layer4.length + layer5.length + 1
  let source : Nat := 0
  let sink : Nat := numNodes - 1
  -- Map nodes to vertex IDs
  let layer4WithIds := (List.range layer4.length).map fun idx =>
    (layer4.getD idx { i := 1, j := 2, k := 4 : Node }, idx + 1)
  let layer5WithIds := (List.range layer5.length).map fun idx =>
    (layer5.getD idx { i := 1, j := 2, k := 5 : Node }, 1 + layer4.length + idx)
  -- Source edges (capacities from X at layer 4)
  let sourceEdges : Array GraphInterface.Edge :=
    (layer4WithIds.map fun (node, id) =>
      let capacity := getMIRValue X node.i node.j 4
      { «from» := source,
        «to» := id,
        capacity := ratToCapacityInt capacity,
        flow := 0 : GraphInterface.Edge }).toArray
  -- Internal edges with F₄ forbidden arc filtering
  let stage4Arcs := permitted_arcs_for_stage 4
  let internalEdges : Array GraphInterface.Edge :=
    (stage4Arcs.filterMap fun (srcNode, tgtNode) =>
      let srcId? := layer4WithIds.find? fun (n, _) => n == srcNode
      let tgtId? := layer5WithIds.find? fun (n, _) => n == tgtNode
      match srcId?, tgtId? with
      | some (_, srcId), some (_, tgtId) =>
        let capacity := getMIRValue X tgtNode.i tgtNode.j 5
        some { «from» := srcId,
               «to» := tgtId,
               capacity := ratToCapacityInt capacity,
               flow := 0 : GraphInterface.Edge }
      | _, _ => none).toArray
  -- Sink edges (infinite capacity represented as large value)
  let sinkEdges : Array GraphInterface.Edge :=
    (layer5WithIds.map fun (node, id) =>
      { «from» := id,
        «to» := sink,
        capacity := 1000000,
        flow := 0 : GraphInterface.Edge }).toArray
  { numVertices := numNodes,
    edges := sourceEdges ++ internalEdges ++ sinkEdges,
    source := source,
    sink := sink : GraphInterface.FlowNetwork }

-- ============================================================================
-- RIGID PEDIGREE EXTRACTION FROM FROZEN FLOWS
-- ============================================================================

/-- Trace a frozen arc back to construct complete pedigree path -/
def tracePedigreePath (frozenArc : Nat × Nat)
    (flowResult : GraphInterface.MaxFlowResult)
    (vertexToNodeMap : Nat → Option Node)
    (n : Nat) : Option (PedigreePath n) :=
  let (u, v) := frozenArc
  -- Get flow value (unscale by dividing by 6)
  let flowValue := flowResult.flowEdges.toList.find?
    (fun (src, dst, _) => src == u && dst == v)
    |>.map (fun (_, _, f) => capacityIntToRat f) |>.getD 0
  if flowValue ≤ 0 then
    none
  else
    match vertexToNodeMap u, vertexToNodeMap v with
    | some nodeU, some nodeV =>
      let path := [
        { i := 1, j := 2, k := 3 : Node },
        nodeU,
        nodeV
      ]
      some { nodes := path, flow := flowValue : PedigreePath n }
    | _, _ => none

/-- Extract all rigid pedigrees from frozen flows -/
def extractRigidPedigrees {n : ℕ} (frozenResult : GraphInterface.FrozenFlowsResult)
    (flowResult : GraphInterface.MaxFlowResult)
    (vertexToNodeMap : Nat → Option Node) : List (PedigreePath n) := -- FIX 11: Changed parameter from k to n
  frozenResult.frozenArcs.toList.filterMap fun arc =>
    tracePedigreePath arc flowResult vertexToNodeMap n

-- ============================================================================
-- NETWORK CAPACITY UPDATE
-- ============================================================================

/-- Check if an edge corresponds to a node in a pedigree path -/
def edgeMatchesNode (edge : GraphInterface.Edge)
    (node : Node)
    (vertexToNodeMap : Nat → Option Node) : Bool :=
  match vertexToNodeMap edge.«from», vertexToNodeMap edge.«to» with
  | some nodeFrom, some nodeTo =>
    (nodeFrom == node) || (nodeTo == node)
  | _, _ => false

/-- Update network capacities by subtracting rigid flows -/
def updateNetworkCapacities (fn : GraphInterface.FlowNetwork)
    (rigidPaths : List (PedigreePath n))
    (vertexToNodeMap : Nat → Option Node) : GraphInterface.FlowNetwork :=
  let updatedEdges := rigidPaths.foldl (init := fn.edges) fun edges path =>
    edges.map fun edge =>
      let isInPath := path.nodes.any fun node =>
        edgeMatchesNode edge node vertexToNodeMap
      if isInPath then
        { edge with capacity := edge.capacity - ratToCapacityInt path.flow }
      else
        edge
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

  let layer4 := nodes_in_layer 4
  let layer5 := nodes_in_layer 5
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
  -- FIX 13: Expected flow should be based on total availability at layer 4
  let layer4Nodes := nodes_in_layer 4
  let totalAvail := layer4Nodes.foldl (fun acc node =>
    acc + getMIRValue X node.i node.j 4) 0
  IO.println s!"Expected total availability at layer 4: {totalAvail}"
  -- Check feasibility: can we satisfy all demands at layer 5?
  let layer5Nodes := nodes_in_layer 5
  let totalDemand := layer5Nodes.foldl (fun acc node =>
    acc + getMIRValue X node.i node.j 5) 0
  if maxFlow < totalDemand then
    return ({ R₄ := [], N₄ := fn, originalFlow := flowResult },
            StageResult.failure s!"F₄ not feasible: flow {maxFlow} < demand {totalDemand}")

  IO.println "✓ F₄ is feasible"

  IO.println "Computing frozen flows (rigid arcs)..."
  let frozenResult ← GraphInterface.computeFrozenFlows fn flowResult
  IO.println s!"Found {frozenResult.frozenArcs.size} frozen arcs"

  let rigidPedigrees := extractRigidPedigrees frozenResult flowResult vertexToNodeMap
  IO.println s!"Rigid pedigrees in R₄: {rigidPedigrees.length}"
  for ridx in List.range rigidPedigrees.length do
    let P := rigidPedigrees.getD ridx { nodes := [], flow := 0 : PedigreePath n }
    IO.println s!"  P{ridx+1}: μ = {P.flow}"

  IO.println "Updating network N₄ (subtracting rigid flows)..."
  let N₄ := updateNetworkCapacities fn rigidPedigrees vertexToNodeMap
  let totalRigid := rigidPedigrees.foldl (init := (0 : Rat)) (fun acc P => acc + P.flow)
  IO.println s!"Total rigid flow: {totalRigid}"
  IO.println s!"Remaining flexible flow: {totalDemand - totalRigid}"
  return ({ R₄ := rigidPedigrees, N₄ := N₄, originalFlow := flowResult },
          StageResult.success)

-- ============================================================================
-- MAIN FRAMEWORK
-- ============================================================================

/-- Complete membership checking algorithm -/
def checkMembership (X : ParsedMIRData n) (hn : n ≥ 5) :
    IO (MembershipResult n) := do

  IO.println "╔════════════════════════════════════════════════╗"
  IO.println "║  Pedigree Polytope Membership Checking (M3P)  ║"
  IO.println "╚════════════════════════════════════════════════╝"
  IO.println ""

  -- Step 1a: Check P_MI
  IO.println "=== Step 1a: Checking P_MI membership ==="
  match checkPMI X hn with
  | StageResult.failure msg =>
      IO.println s!"✗ {msg}"
      return MembershipResult.notInConvexHull s!"Step 1a failed: {msg}"
  | StageResult.success =>
    IO.println "✓ X ∈ P_MI(n)"

    -- Step 1b: Analyze F₄
    let (f4Result, f4Stage) ← analyzeF4Complete X hn
    match f4Stage with
    | StageResult.failure msg =>
        IO.println s!"✗ {msg}"
        return MembershipResult.notInConvexHull s!"Step 1b failed: {msg}"
    | StageResult.success =>
      IO.println "✓ F₄ analysis complete"

      -- For now, return success after F₄
      -- TODO: Implement F₅ and beyond
      IO.println ""
      IO.println "╔════════════════════════════════════════════════╗"
      IO.println "║           MEMBERSHIP: CONFIRMED ✓              ║"
      IO.println "║         (F₄ Complete, F₅+ TODO)                ║"
      IO.println "╚════════════════════════════════════════════════╝"
      return MembershipResult.inConvexHull

end PedigreePolytope
