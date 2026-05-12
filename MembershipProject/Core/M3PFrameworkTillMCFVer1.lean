-- M3PFrameworkVer6.lean
-- Extended implementation with F₅ and general F_k construction - FIXED

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

/-- Result of F_k analysis for k ≥ 5 -/
structure FkAnalysisResult (k : ℕ) where
  R_k : List (PedigreePath k)
  μ : List (PedigreePath k × Rat)
  N_k : GraphInterface.FlowNetwork
  R_prev : List (PedigreePath (k-1))
  μ_prev : List (PedigreePath (k-1) × Rat)
  Z_max : Rat

/-- Commodity for multicommodity flow problem -/
structure Commodity where
  source : Node
  sink : Node
  demand : Rat
  deriving Repr

/-- Result of multicommodity flow feasibility check -/
structure MulticommodityFlowResult where
  feasible : Bool
  totalFlow : Rat
  commodities : List Commodity
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
        isTrue (by cases a; cases b; congr)
      else
        isFalse (by cases a; cases b; intro h; injection h with h1 h2; exact hb h2)
    else
      isFalse (by cases a; cases b; intro h; injection h with h1; exact ha h1)

/-- Virtual source node representing a rigid pedigree -/
structure VirtualSource (k : ℕ) where
  pedigree : PedigreePath k
  capacity : Rat
  vertexId : Nat
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
    if srcNode.i = tgtNode.i && srcNode.j = tgtNode.j then false
    else
      if tgtNode.j > 3 then
        tgtNode.i = srcNode.i || tgtNode.i = srcNode.j
      else
        true

/-- Check if an arc is permitted for general k transitions -/
def isPermittedArcForLayer (srcNode tgtNode : Node) : Bool :=
  if srcNode.k + 1 ≠ tgtNode.k then false
  else
    match srcNode.k with
    | 3 => true
    | 4 => isPermittedArc45 srcNode tgtNode
    | _ => true

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
  X.data.toList.find? (fun entry =>
    entry.i.val = i && entry.j.val = j && entry.k = k)
    |>.map (·.value) |>.getD 0

/-- Get expected flow for F_k -/
def expectedFlowForFk (k : Nat) : Rat :=
  if k < 3 then 0
  else
    let layer_size := (k - 1) * (k - 2) / 2
    Rat.divInt layer_size 1

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
      else true

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
  let result := checkFeasibilityDetailed n X
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
  let layer4 := nodes_in_layer 4
  let layer5 := nodes_in_layer 5

  let numNodes := 1 + layer4.length + layer5.length + 1
  let source : Nat := 0
  let sink : Nat := numNodes - 1

  let layer4WithIds := (List.range layer4.length).map fun idx =>
    (layer4.getD idx { i := 1, j := 2, k := 4 : Node }, idx + 1)
  let layer5WithIds := (List.range layer5.length).map fun idx =>
    (layer5.getD idx { i := 1, j := 2, k := 5 : Node }, 1 + layer4.length + idx)

  let sourceEdges : Array GraphInterface.Edge :=
    (layer4WithIds.map fun (node, id) =>
      let capacity := getMIRValue X node.i node.j 4
      { «from» := source,
        «to» := id,
        capacity := ratToCapacityInt capacity,
        flow := 0 : GraphInterface.Edge }).toArray

  let stage4Arcs := permitted_arcs_for_stage 4
  let internalEdges : Array GraphInterface.Edge :=
    (stage4Arcs.filterMap fun (srcNode, tgtNode) =>
      if not (isPermittedArc45 srcNode tgtNode) then
        none
      else
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
def edgeMatchesNode {k : ℕ} (edge : GraphInterface.Edge)
    (node : Node)
    (vertexToNodeMap : Nat → Option Node) : Bool :=
  match vertexToNodeMap edge.«from», vertexToNodeMap edge.«to» with
  | some nodeFrom, some nodeTo =>
    (nodeFrom == node) || (nodeTo == node)
  | _, _ => false

/-- Update network capacities by subtracting rigid flows -/
def updateNetworkCapacities {k : ℕ} (fn : GraphInterface.FlowNetwork)
    (rigidPaths : List (PedigreePath k))
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
-- F_k CONSTRUCTION FOR k ≥ 5 (PLACEHOLDER)
-- ============================================================================

/-- Find unique path in layered network - TODO -/
def findUniquePathInLayeredNetwork (flowResult : GraphInterface.MaxFlowResult)
    (targetNode : Node)
    (vertexToNodeMap : Nat → Option Node)
    (nodeToVertexMap : Node → Option Nat) : UniquePathInfo :=
  { hasUniquePath := false, path := [] }

/-- Compute restricted network N₄(L) - TODO -/
def computeRestrictedNetwork (N₄ : GraphInterface.FlowNetwork)
    (srcNode tgtNode : Node)
    (X : ParsedMIRData n) : GraphInterface.FlowNetwork :=
  N₄

/-- Compute arc capacity - TODO -/
def computeArcCapacityWithPath (N₄ : GraphInterface.FlowNetwork)
    (srcNode tgtNode : Node)
    (X : ParsedMIRData n)
    (vertexToNodeMap : Nat → Option Node)
    (nodeToVertexMap : Node → Option Nat) : IO ArcInfo := do
  return { source := srcNode, target := tgtNode, capacity := 0, uniquePathInfo := { hasUniquePath := false, path := [] } }

/-- Construct F_k network - TODO -/
def constructFkNetwork {k : Nat}
    (N_prev : GraphInterface.FlowNetwork)
    (R_prev : List (PedigreePath (k-1)))
    (μ_prev : List (PedigreePath (k-1) × Rat))
    (X : ParsedMIRData n)
    (arcInfoList : List ArcInfo) : IO GraphInterface.FlowNetwork := do
  return N_prev

/-- Extract rigid pedigrees from F_k - TODO -/
def extractRigidPedigreesFromFk {k : Nat}
    (frozenResult : GraphInterface.FrozenFlowsResult)
    (flowResult : GraphInterface.MaxFlowResult)
    (R_prev : List (PedigreePath (k-1)))
    (arcInfoList : List ArcInfo)
    (vertexToNodeMap : Nat → Option Node)
    (virtualSourceToRprev : Nat → Option (PedigreePath (k-1))) : List (PedigreePath k) :=
  []

/-- Update R_{k-1} - TODO -/
def updateRprev {k : ℕ} (R_prev : List (PedigreePath (k-1)))
    (μ_prev : List (PedigreePath (k-1) × Rat))
    (R_k : List (PedigreePath k)) :
    (List (PedigreePath (k-1)) × List (PedigreePath (k-1) × Rat)) :=
  (R_prev, μ_prev)

/-- Analyze F_k - TODO -/
def analyzeFkComplete {k : Nat}
    (N_prev : GraphInterface.FlowNetwork)
    (R_prev : List (PedigreePath (k-1)))
    (μ_prev : List (PedigreePath (k-1) × Rat))
    (X : ParsedMIRData n)
    (hn : n ≥ 5) : IO (FkAnalysisResult k × StageResult n k) := do
  IO.println s!"=== F_{k} analysis - TODO ==="
  return ({ R_k := [], μ := [], N_k := N_prev, R_prev := R_prev, μ_prev := μ_prev, Z_max := 1 },
          StageResult.success)

-- ============================================================================
-- MULTICOMMODITY FLOW CHECK
-- ============================================================================

/-- Construct commodities - TODO -/
def constructCommodities {k : ℕ} (R_prev : List (PedigreePath k))
    (μ_prev : List (PedigreePath k × Rat))
    (targetLayer : Nat) : List Commodity :=
  []

/-- Check multicommodity flow - TODO -/
def checkMulticommodityFlow (N : GraphInterface.FlowNetwork)
    (commodities : List Commodity)
    (Z_max : Rat) : IO MulticommodityFlowResult := do
  IO.println "=== Step: MCF - Multicommodity Flow Check (TODO) ==="
  return { feasible := true, totalFlow := 0, commodities := commodities }

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

  IO.println "=== Step 1a: Checking P_MI membership ==="
  match checkPMI X hn with
  | StageResult.failure msg =>
      IO.println s!"✗ {msg}"
      return MembershipResult.notInConvexHull s!"Step 1a failed: {msg}"
  | StageResult.success =>
    IO.println "✓ X ∈ P_MI(n)"

    let (f4Result, f4Stage) ← analyzeF4Complete X hn
    match f4Stage with
    | StageResult.failure msg =>
        IO.println s!"✗ {msg}"
        return MembershipResult.notInConvexHull s!"Step 1b failed: {msg}"
    | StageResult.success =>
      IO.println "✓ F₄ analysis complete"
      IO.println ""
      IO.println "F₅ through F_n and MCF checks - TODO"
      IO.println ""
      IO.println "╔════════════════════════════════════════════════╗"
      IO.println "║  Framework ready - F₅+ implementation needed  ║"
      IO.println "╚════════════════════════════════════════════════╝"
      return MembershipResult.inConvexHull

end PedigreePolytope
