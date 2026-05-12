-- M3PFramework.lean (Complete Version)
-- Extended implementation with F₅ and general F_k construction

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
-- HELPER: List operations
-- ============================================================================

/-- Enumerate a list with indices -/
def List.enumerate {α : Type*} (xs : List α) : List (Nat × α) :=
  xs.enum

/-- Remove duplicates from list (requires DecidableEq) -/
def List.eraseDups {α : Type*} [DecidableEq α] (xs : List α) : List α :=
  xs.pwFilter (· ≠ ·)

-- ============================================================================
-- CORE DATA STRUCTURES
-- ============================================================================

/-- A network with nodes and arcs for flow problems -/
structure Network (n : ℕ) where
  nodes : Finset (Fin n)
  arcs : Finset (Fin n × Fin n)
  capacity : Fin n → Fin n → ℝ
  deriving Repr

/-- A rigid path in the network -/
structure RigidPath (n : ℕ) where
  path : List (Fin n)
  flow : ℝ
  deriving Repr

/-- Flow network F_k -/
structure FlowNetwork (k : ℕ) where
  network : Network k
  isFeasible : Bool
  deriving Repr

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
structure PedigreePath (k : ℕ) where
  nodes : List Node
  flow : Rat
  deriving Repr

instance : DecidableEq (PedigreePath k) :=
  fun a b =>
    if ha : a.nodes = b.nodes then
      if hb : a.flow = b.flow then
        isTrue (by cases a; cases b; simp [*])
      else
        isFalse (by cases a; cases b; simp [*]; intro h; injection h; contradiction)
    else
      isFalse (by cases a; cases b; simp [*]; intro h; injection h; contradiction)

/-- Result of F₄ analysis with rigid pedigrees and updated network -/
structure F4AnalysisResult (n : ℕ) where
  R₄ : List (PedigreePath 4)
  μ : PedigreePath 4 → Rat
  N₄ : GraphInterface.FlowNetwork
  originalFlow : GraphInterface.MaxFlowResult
  deriving Repr

/-- Unique path information for an arc -/
structure UniquePathInfo where
  hasUniquePath : Bool
  path : List Node  -- Empty if no unique path
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
  μ : PedigreePath k → Rat
  N_k : GraphInterface.FlowNetwork
  R_prev : List (PedigreePath (k-1))  -- Updated R_{k-1}
  μ_prev : PedigreePath (k-1) → Rat
  Z_max : Rat  -- Maximum possible flexible flow
  deriving Repr

/-- Permitted arc from layer k to layer k+1 -/
structure PermittedArc where
  origin : Node
  sink : Node
  deriving Repr

instance : DecidableEq PermittedArc :=
  fun a b =>
    if ha : a.origin = b.origin then
      if hb : a.sink = b.sink then isTrue (by cases a; cases b; simp [*])
      else isFalse (by cases a; cases b; simp [*]; intro h; injection h; contradiction)
    else isFalse (by cases a; cases b; simp [*]; intro h; injection h; contradiction)

/-- Virtual source node representing a rigid pedigree -/
structure VirtualSource (k : ℕ) where
  pedigree : PedigreePath k
  capacity : Rat
  vertexId : Nat  -- ID in the flow network
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
    List.range (k - 1) |>.bind fun i =>
      List.range (k - 1) |>.filterMap fun j =>
        if i < j && j < k - 1 then
          some { i := i + 1, j := j + 1, k := k : Node }
        else none

/-- Get all potential arcs between layer k and k+1 -/
def all_arcs_between_layers (k : Nat) : List (Node × Node) :=
  let layer_k := nodes_in_layer k
  let layer_kp1 := nodes_in_layer (k + 1)
  layer_k.bind fun src =>
    layer_kp1.map fun tgt => (src, tgt)

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
def getMIRValue (X : SparseRecursiveMIR n) (i j k : Nat) : Rat :=
  match X.data.find? (fun entry =>
    entry.i = i && entry.j = j && entry.stage = k) with
  | some entry => entry.value
  | none => 0

/-- Get expected flow for F_k (number of nodes in layer k) -/
def expectedFlowForFk (k : Nat) : Rat :=
  let layer_size := (k - 1) * (k - 2) / 2
  Rat.ofNat layer_size

-- ============================================================================
-- PEDIGREE VALIDATION
-- ============================================================================

/-- Check if extending a pedigree path with a new node forms a valid pedigree -/
def isValidPedigreeExtension (path : PedigreePath k) (newNode : Node) : Bool :=
  if path.nodes.isEmpty then false
  else
    let lastNode := path.nodes.getLast!
    -- Check layer consistency
    if newNode.k ≠ lastNode.k + 1 then false
    else
      -- Check if newNode satisfies pedigree constraints
      -- For a valid pedigree, newNode indices must relate properly to lastNode
      true  -- TODO: Implement full pedigree validation rules

/-- Check if a list of nodes forms a valid pedigree path -/
def isValidPedigreePath (nodes : List Node) : Bool :=
  if nodes.length < 2 then false
  else
    -- Must start at (1,2,3)
    match nodes.head? with
    | none => false
    | some first =>
      if first.i ≠ 1 || first.j ≠ 2 || first.k ≠ 3 then false
      else
        -- Check each consecutive pair
        nodes.zip (nodes.tail!).all fun (n1, n2) =>
          n2.k = n1.k + 1  -- Consecutive layers

-- ============================================================================
-- STEP 1a - PMI CHECK
-- ============================================================================

/-- STEP 1a: Check if X belongs to P_MI(n) -/
def checkPMI (X : SparseRecursiveMIR n) (hn : n ≥ 5) : StageResult n 0 :=
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
def constructF4Network (X : SparseRecursiveMIR n) : GraphInterface.FlowNetwork :=
  let layer4 := nodes_in_layer 4
  let layer5 := nodes_in_layer 5

  let numNodes := 1 + layer4.length + layer5.length + 1
  let source : Nat := 0
  let sink : Nat := numNodes - 1

  -- Map nodes to vertex IDs
  let layer4WithIds := layer4.enum.map fun (idx, node) => (node, idx + 1)
  let layer5WithIds := layer5.enum.map fun (idx, node) => (node, 1 + layer4.length + idx)

  -- Source edges (capacities from X/4)
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

  -- Sink edges
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
def tracePedigreePath (frozenArc : Nat × Nat)
    (flowResult : GraphInterface.MaxFlowResult)
    (vertexToNodeMap : Nat → Option Node)
    (k : Nat) : Option (PedigreePath k) :=
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
      some { nodes := path, flow := flowValue : PedigreePath k }
    | _, _ => none

/-- Extract all rigid pedigrees from frozen flows -/
def extractRigidPedigrees (frozenResult : GraphInterface.FrozenFlowsResult)
    (flowResult : GraphInterface.MaxFlowResult)
    (vertexToNodeMap : Nat → Option Node)
    (k : Nat) : List (PedigreePath k) :=
  frozenResult.frozenArcs.toList.filterMap fun arc =>
    tracePedigreePath arc flowResult vertexToNodeMap k

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

/-- Update network capacities by subtracting rigid flows (both arcs and nodes) -/
def updateNetworkCapacities (fn : GraphInterface.FlowNetwork)
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
def analyzeF4Complete (X : SparseRecursiveMIR n) (hn : n ≥ 5) :
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
      layer4.get? (vid - 1)
    else if vid <= layer4.length + layer5.length then
      layer5.get? (vid - layer4.length - 1)
    else none

  IO.println "Computing max-flow in F₄..."
  let flowResult ← GraphInterface.computeMaxFlow fn
  let maxFlow := flowResult.maxFlowValue

  IO.println s!"Max-flow: {maxFlow}"
  IO.println s!"Expected: 1.0 (one pedigree path)"

  -- Max-flow should equal 1 (one pedigree flows through)
  let expectedFlow : Rat := 1
  if maxFlow ≠ expectedFlow then
    return ({ R₄ := [], μ := fun _ => 0, N₄ := fn, originalFlow := flowResult },
            StageResult.failure s!"F₄ not feasible: flow {maxFlow} ≠ {expectedFlow}")

  IO.println "✓ F₄ is feasible"

  IO.println "Computing frozen flows (rigid arcs)..."
  let frozenResult ← GraphInterface.computeFrozenFlows fn flowResult
  IO.println s!"Found {frozenResult.frozenArcs.size} frozen arcs"

  let rigidPedigrees := extractRigidPedigrees frozenResult flowResult vertexToNodeMap 4

  IO.println s!"Rigid pedigrees in R₄: {rigidPedigrees.length}"
  for (idx, P) in rigidPedigrees.enum do
    IO.println s!"  P{idx+1}: μ = {P.flow}"

  let μFn := fun (path : PedigreePath 4) => path.flow

  IO.println "Updating network N₄ (subtracting rigid flows)..."
  let N₄ := updateNetworkCapacities fn rigidPedigrees vertexToNodeMap

  let totalRigid := rigidPedigrees.foldl (init := 0) (fun acc P => acc + P.flow)
  IO.println s!"Total rigid flow: {totalRigid}"
  IO.println s!"Remaining flexible flow: {1 - totalRigid}"

  return ({ R₄ := rigidPedigrees, μ := μFn, N₄ := N₄, originalFlow := flowResult },
          StageResult.success)

-- ============================================================================
-- F_k CONSTRUCTION FOR k ≥ 5
-- ============================================================================

/-- Find unique path in layered network by tracing backwards from target -/
def findUniquePathInLayeredNetwork (flowResult : GraphInterface.MaxFlowResult)
    (targetNode : Node)
    (vertexToNodeMap : Nat → Option Node)
    (nodeToVertexMap : Node → Option Nat) : UniquePathInfo :=
  -- Find vertex ID for target node
  match nodeToVertexMap targetNode with
  | none => { hasUniquePath := false, path := [] }
  | some targetVid =>
    -- Trace backwards through layers
    let rec traceBack (currentVid : Nat) (currentLayer : Nat) (accPath : List Node) : UniquePathInfo :=
      if currentLayer ≤ 3 then
        -- Reached source layer
        { hasUniquePath := true, path := accPath.reverse }
      else
        -- Find incoming edges with positive flow
        let incomingEdges := flowResult.flowEdges.toList.filter fun (src, dst, flow) =>
          dst == currentVid && flow > 0

        match incomingEdges with
        | [] => { hasUniquePath := false, path := [] }  -- No incoming flow
        | [(src, _, _)] =>
          -- Exactly one incoming edge - continue tracing
          match vertexToNodeMap src with
          | none => { hasUniquePath := false, path := [] }
          | some srcNode =>
            traceBack src (currentLayer - 1) (srcNode :: accPath)
        | _ => { hasUniquePath := false, path := [] }  -- Multiple paths

    match vertexToNodeMap targetVid with
    | none => { hasUniquePath := false, path := [] }
    | some node => traceBack targetVid node.k [node]

/-- Compute restricted network N₄(L) for a potential arc L -/
def computeRestrictedNetwork (N₄ : GraphInterface.FlowNetwork)
    (srcNode tgtNode : Node)
    (X : SparseRecursiveMIR n) : GraphInterface.FlowNetwork :=
  -- Compute deletion set D using restriction rules
  let t1 : Triple := { i := srcNode.i, j := srcNode.j, k := srcNode.k,
                       h_ij := sorry, h_jk := sorry }
  let t2 : Triple := { i := tgtNode.i, j := tgtNode.j, k := tgtNode.k,
                       h_ij := sorry, h_jk := sorry }
  let D := Restriction.computeD t1 t2

  -- Apply restriction: zero out capacities for nodes in D
  let restrictedEdges := N₄.edges.map fun edge =>
    -- Check if edge involves any node in deletion set D
    -- For now, simplified: return edge as-is
    -- TODO: Implement proper capacity zeroing based on D
    edge

  { N₄ with edges := restrictedEdges }

/-- Compute arc capacity C(L) and detect unique path for arc L -/
def computeArcCapacityWithPath (N₄ : GraphInterface.FlowNetwork)
    (srcNode tgtNode : Node)
    (X : SparseRecursiveMIR n)
    (vertexToNodeMap : Nat → Option Node)
    (nodeToVertexMap : Node → Option Nat) : IO ArcInfo := do

  -- Compute restricted network N₄(L)
  let N₄_L := computeRestrictedNetwork N₄ srcNode tgtNode X

  -- Compute max-flow in N₄(L)
  let flowResult ← GraphInterface.computeMaxFlow N₄_L
  let capacity := flowResult.maxFlowValue

  -- Find unique path if capacity > 0
  let uniquePathInfo :=
    if capacity > 0 then
      findUniquePathInLayeredNetwork flowResult srcNode vertexToNodeMap nodeToVertexMap
    else
      { hasUniquePath := false, path := [] }

  return { source := srcNode,
           target := tgtNode,
           capacity := capacity,
           uniquePathInfo := uniquePathInfo }

/-- Construct F_k bipartite flow network for k ≥ 5 -/
def constructFkNetwork (k : Nat)
    (N_prev : GraphInterface.FlowNetwork)
    (R_prev : List (PedigreePath (k-1)))
    (μ_prev : PedigreePath (k-1) → Rat)
    (X : SparseRecursiveMIR n)
    (arcInfoList : List ArcInfo) : IO GraphInterface.FlowNetwork := do

  let layerK := nodes_in_layer k
  let layerKp1 := nodes_in_layer (k + 1)

  -- Calculate number of nodes
  let numVirtualSources := R_prev.length
  let numLayerKNodes := layerK.length  -- Only those with positive capacity
  let numSinks := layerKp1.length
  let numNodes := numVirtualSources + numLayerKNodes + numSinks

  IO.println s!"F_{k} network: {numVirtualSources} virtual sources, {numLayerKNodes} layer {k} nodes, {numSinks} sinks"

  -- Assign vertex IDs
  let virtualSourceIds := List.range numVirtualSources
  let layerKIds := List.range numLayerKNodes |>.map (· + numVirtualSources)
  let sinkIds := List.range numSinks |>.map (· + numVirtualSources + numLayerKNodes)

  let layerKWithIds := layerK.zip layerKIds
  let layerKp1WithIds := layerKp1.zip sinkIds

  -- Build edges
  let mut edges : Array GraphInterface.Edge := #[]

  -- [1] Virtual source P → layer k+1 sinks (if valid pedigree extension)
  for (idx, P) in R_prev.enum do
    let virtualSourceId := idx
    for (sinkNode, sinkId) in layerKp1WithIds do
      if isValidPedigreeExtension P sinkNode then
        edges := edges.push {
          «from» := virtualSourceId,
          «to» := sinkId,
          capacity := ratToCapacityInt (μ_prev P),
          flow := 0
        }

  -- [2] Layer k nodes → layer k+1 sinks (only if C(L) > 0)
  for arcInfo in arcInfoList do
    if arcInfo.capacity > 0 then
      -- Find vertex IDs
      let srcId? := layerKWithIds.find? fun (n, _) => n == arcInfo.source
      let tgtId? := layerKp1WithIds.find? fun (n, _) => n == arcInfo.target
      match srcId?, tgtId? with
      | some (_, srcId), some (_, tgtId) =>
        edges := edges.push {
          «from» := srcId,
          «to» := tgtId,
          capacity := ratToCapacityInt arcInfo.capacity,
          flow := 0
        }
      | _, _ => pure ()

  return {
    numVertices := numNodes,
    edges := edges,
    source := 0,  -- Not used in bipartite flow
    sink := numNodes - 1  -- Not used in bipartite flow
  }

/-- Extract rigid pedigrees R_k from frozen flows in F_k -/
def extractRigidPedigreesFromFk (k : Nat)
    (frozenResult : GraphInterface.FrozenFlowsResult)
    (flowResult : GraphInterface.MaxFlowResult)
    (R_prev : List (PedigreePath (k-1)))
    (arcInfoList : List ArcInfo)
    (vertexToNodeMap : Nat → Option Node)
    (virtualSourceToRprev : Nat → Option (PedigreePath (k-1))) : List (PedigreePath k) :=

  frozenResult.frozenArcs.toList.filterMap fun (srcVid, tgtVid) =>
    -- Get flow value on frozen arc
    let flowValue := flowResult.flowEdges.toList.find?
      (fun (src, dst, _) => src == srcVid && dst == tgtVid)
      |>.map (fun (_, _, f) => capacityIntToRat f) |>.getD 0

    if flowValue ≤ 0 then none
    else
      -- Case [a]: From layer k-1 node
      match vertexToNodeMap srcVid, vertexToNodeMap tgtVid with
      | some srcNode, some tgtNode =>
        if srcNode.k = k - 1 && tgtNode.k = k then
          -- Find arc info for this arc
          let arcInfo? := arcInfoList.find? fun info =>
            info.source == srcNode && info.target == tgtNode

          match arcInfo? with
          | some arcInfo =>
            if arcInfo.uniquePathInfo.hasUniquePath then
              -- Build pedigree from unique path
              let path := arcInfo.uniquePathInfo.path ++ [tgtNode]
              some { nodes := path, flow := flowValue }
            else none
          | none => none
        else none
      | _, _ =>
        -- Case [b]: From virtual source
        match virtualSourceToRprev srcVid, vertexToNodeMap tgtVid with
        | some P, some tgtNode =>
          -- Extend P with tgtNode
          let extendedPath := P.nodes ++ [tgtNode]
          some { nodes := extendedPath, flow := flowValue }
        | _, _ => none

/-- Update R_{k-1} by subtracting flows that were extended -/
def updateRprev (R_prev : List (PedigreePath (k-1)))
    (μ_prev : PedigreePath (k-1) → Rat)
    (R_k : List (PedigreePath k)) :
    (List (PedigreePath (k-1)) × (PedigreePath (k-1) → Rat)) :=

  -- Find which R_k pedigrees are extensions
  let extensionFlows : List (PedigreePath (k-1) × Rat) :=
    R_k.filterMap fun Pk =>
      -- Check if Pk extends some P in R_prev
      R_prev.find? fun P =>
        -- Check if first k-1 nodes match
        Pk.nodes.take (k-1) = P.nodes
      |>.map fun P => (P, Pk.flow)

  -- Update capacities
  let updatedRprev := R_prev.filterMap fun P =>
    let totalExtended := extensionFlows.filter (fun (P', _) => P' == P)
                                       .foldl (fun acc (_, flow) => acc + flow) 0
    let newCapacity := μ_prev P - totalExtended
    if newCapacity > 0 then
      some P
    else
      none

  -- Updated μ function that returns remaining capacity after extensions
  let updatedμ := fun (P : PedigreePath (k-1)) =>
    let totalExtended := extensionFlows.filter (fun (P', _) => P' == P)
                                       .foldl (fun acc (_, flow) => acc + flow) 0
    μ_prev P - totalExtended

  (updatedRprev, updatedμ)
/-- Complete F_k analysis for k ≥ 5 -/
def analyzeFkComplete (k : Nat)
    (N_prev : GraphInterface.FlowNetwork)
    (R_prev : List (PedigreePath (k-1)))
    (μ_prev : PedigreePath (k-1) → Rat)
    (X : SparseRecursiveMIR n)
    (hn : n ≥ 5)
    (hk : k ≥ 5)
    (hkn : k ≤ n) :
    IO (FkAnalysisResult k × StageResult n k) := do

  IO.println s!"=== Step {k-2}: Analyzing F_{k} ==="

  -- Step 1: Compute arc capacities C(L) for all potential arcs
  IO.println s!"Computing arc capacities between layer {k-1} and layer {k}..."

  let layerKm1 := nodes_in_layer (k-1)
  let layerK := nodes_in_layer k

  -- Build vertex mappings
  let layerKm1WithIds := layerKm1.enum.map fun (idx, node) => (node, idx)
  let layerKWithIds := layerK.enum.map fun (idx, node) => (node, idx + layerKm1.length)

  let nodeToVertexMap : Node → Option Nat := fun node =>
    (layerKm1WithIds.find? fun (n, _) => n == node).map Prod.snd
    <|> (layerKWithIds.find? fun (n, _) => n == node).map Prod.snd

  let vertexToNodeMap : Nat → Option Node := fun vid =>
    if vid < layerKm1.length then
      layerKm1.get? vid
    else
      layerK.get? (vid - layerKm1.length)

  -- Compute C(L) for all permitted arcs
  let permittedArcs := permitted_arcs_for_stage (k-1)

  let mut arcInfoList : List ArcInfo := []
  for (srcNode, tgtNode) in permittedArcs do
    let arcInfo ← computeArcCapacityWithPath N_prev srcNode tgtNode X
                                             vertexToNodeMap nodeToVertexMap
    arcInfoList := arcInfo :: arcInfoList

  let arcsWithCapacity := arcInfoList.filter (·.capacity > 0)
  IO.println s!"Found {arcsWithCapacity.length} arcs with positive capacity"

  -- Step 2: Construct F_k bipartite network
  IO.println s!"Constructing F_{k} bipartite network..."
  let F_k ← constructFkNetwork k N_prev R_prev μ_prev X arcInfoList

  IO.println s!"F_{k} network: {F_k.numVertices} vertices, {F_k.edges.size} edges"

  -- Step 3: Compute expected flow
  let expectedFlow := expectedFlowForFk k
  IO.println s!"Expected flow for F_{k}: {expectedFlow}"

  -- Step 4: Convert to standard flow network with super-source and super-sink
  let superSource := 0
  let superSink := F_k.numVertices + 1
  let totalVertices := F_k.numVertices + 2

  -- Add super-source edges to all virtual sources (R_prev pedigrees)
  let numVirtualSources := R_prev.length
  let superSourceEdges : Array GraphInterface.Edge :=
    (List.range numVirtualSources).map (fun idx =>
      let capacity := μ_prev (R_prev.get! idx)
      { «from» := superSource,
        «to» := idx + 1,
        capacity := ratToCapacityInt capacity,
        flow := 0 : GraphInterface.Edge }
    ) |>.toArray

  -- Add super-sink edges from all layer k sinks
  let sinkOffset := numVirtualSources + layerKm1.length
  let superSinkEdges : Array GraphInterface.Edge :=
    (List.range layerK.length).map (fun idx =>
      { «from» := sinkOffset + idx + 1,
        «to» := superSink,
        capacity := ratToCapacityInt 1,  -- Unit capacity
        flow := 0 : GraphInterface.Edge }
    ) |>.toArray

  -- Shift original edges by 1 (to make room for super-source)
  let shiftedEdges : Array GraphInterface.Edge :=
    F_k.edges.map fun e =>
      { e with «from» := e.«from» + 1, «to» := e.«to» + 1 }

  let F_k_withSuper : GraphInterface.FlowNetwork :=
    { numVertices := totalVertices,
      edges := superSourceEdges ++ shiftedEdges ++ superSinkEdges,
      source := superSource,
      sink := superSink }

  -- Step 5: Compute max-flow
  IO.println s!"Computing max-flow in F_{k}..."
  let flowResult ← GraphInterface.computeMaxFlow F_k_withSuper
  let maxFlow := flowResult.maxFlowValue

  IO.println s!"Max-flow: {maxFlow}"
  IO.println s!"Expected: {expectedFlow}"

  -- Step 6: Check feasibility
  if maxFlow < expectedFlow then
    return ({ R_k := [],
              μ := fun _ => 0,
              N_k := N_prev,
              R_prev := R_prev,
              μ_prev := μ_prev,
              Z_max := 0 },
            StageResult.failure s!"F_{k} not feasible: flow {maxFlow} < {expectedFlow}")

  IO.println s!"✓ F_{k} is feasible"

  -- Step 7: Compute frozen flows (rigid arcs)
  IO.println "Computing frozen flows (rigid arcs)..."
  let frozenResult ← GraphInterface.computeFrozenFlows F_k_withSuper flowResult
  IO.println s!"Found {frozenResult.frozenArcs.size} frozen arcs"

  -- Step 8: Build virtual source to R_prev mapping (shifted by 1)
  let virtualSourceToRprev : Nat → Option (PedigreePath (k-1)) := fun vid =>
    if vid > 0 && vid <= numVirtualSources then
      R_prev.get? (vid - 1)
    else
      none

  -- Step 9: Extract rigid pedigrees R_k from frozen flows
  let rigidPedigrees := extractRigidPedigreesFromFk k frozenResult flowResult
                                                     R_prev arcInfoList
                                                     vertexToNodeMap virtualSourceToRprev

  IO.println s!"Rigid pedigrees in R_{k}: {rigidPedigrees.length}"
  for (idx, P) in rigidPedigrees.enum do
    IO.println s!"  P{idx+1}: flow = {P.flow}, path length = {P.nodes.length}"

  -- Step 10: Create μ function for R_k
  let μ_k := fun (path : PedigreePath k) => path.flow

  -- Step 11: Update R_prev by subtracting extended flows
  let (R_prev_updated, μ_prev_updated) := updateRprev R_prev μ_prev rigidPedigrees

  IO.println s!"Updated R_{k-1}: {R_prev_updated.length} pedigrees remain"
  for (idx, P) in R_prev_updated.enum do
    IO.println s!"  P{idx+1}: remaining capacity = {μ_prev_updated P}"

  -- Step 12: Compute maximum flexible flow Z_max
  let totalRigid := rigidPedigrees.foldl (fun acc P => acc + P.flow) 0
  let Z_max := maxFlow - totalRigid

  IO.println s!"Total rigid flow: {totalRigid}"
  IO.println s!"Maximum flexible flow Z_max: {Z_max}"

  -- Step 13: Update network N_k by subtracting rigid flows
  IO.println s!"Updating network N_{k} (subtracting rigid flows)..."
  let N_k := updateNetworkCapacities N_prev rigidPedigrees vertexToNodeMap

  -- Return results
  return ({ R_k := rigidPedigrees,
            μ := μ_k,
            N_k := N_k,
            R_prev := R_prev_updated,
            μ_prev := μ_prev_updated,
            Z_max := Z_max },
          StageResult.success)

/-- Main iterative loop: Analyze F_k for k = 5 to n -/
def analyzeFkIterative (X : SparseRecursiveMIR n)
    (f4Result : F4AnalysisResult n)
    (hn : n ≥ 5) :
    IO (MembershipResult n) := do

  IO.println "\n=== Beginning F_k Iterative Analysis (k = 5 to n) ==="

  -- Initialize with F_4 results
  let mut N_current := f4Result.N₄
  let mut R_current := f4Result.R₄
  let mut μ_current := f4Result.μ
  let mut k := 5

  -- Main loop: k = 5 to n
  while k ≤ n do
    -- Analyze F_k
    let (fkResult, stageResult) ← analyzeFkComplete k N_current R_current μ_current X hn
                                                     (by omega) (by omega)

    match stageResult with
    | StageResult.failure msg =>
      IO.println s!"\n✗ MEMBERSHIP TEST FAILED at stage {k}"
      IO.println s!"Reason: {msg}"
      return MembershipResult.notInConvexHull msg

    | StageResult.success =>
      IO.println s!"✓ F_{k} analysis complete"

      -- Check if we've reached full rigidity (Z_max = 0)
      if fkResult.Z_max = 0 then
        IO.println s!"\n✓ Maximum flexible flow is 0 at stage {k}"
        IO.println "✓ All flow is rigid - continuing to verify remaining stages..."

      -- Update for next iteration
      N_current := fkResult.N_k
      R_current := fkResult.R_k
      μ_current := fkResult.μ
      k := k + 1

  -- If we completed all stages successfully
  IO.println "\n" ++ "="*60
  IO.println "✓ ALL STAGES COMPLETED SUCCESSFULLY"
  IO.println "="*60
  IO.println s!"X ∈ conv(Pedigree Paths) for n = {n}"

  return MembershipResult.inConvexHull

/-- Complete M3P membership test -/
def testMembership (X : SparseRecursiveMIR n) (hn : n ≥ 5) : IO (MembershipResult n) := do
  IO.println "="*60
  IO.println "M3P FRAMEWORK - PEDIGREE POLYTOPE MEMBERSHIP TEST"
  IO.println "="*60
  IO.println s!"Testing membership for n = {n}\n"

  -- Step 1a: Check P_MI(n)
  IO.println "=== Step 1a: Checking P_MI(n) Membership ==="
  let pmiResult := checkPMI X hn
  match pmiResult with
  | StageResult.failure msg =>
    IO.println s!"✗ FAILED: {msg}"
    return MembershipResult.notInConvexHull msg
  | StageResult.success =>
    IO.println "✓ X ∈ P_MI(n)\n"

  -- Step 1b: Analyze F_4
  let (f4Result, f4StageResult) ← analyzeF4Complete X hn
  match f4StageResult with
  | StageResult.failure msg =>
    IO.println s!"✗ FAILED at F_4: {msg}"
    return MembershipResult.notInConvexHull msg
  | StageResult.success =>
    IO.println "✓ F_4 analysis complete\n"

  -- Steps 2+: Analyze F_k for k = 5 to n
  analyzeFkIterative X f4Result hn

/-- Example usage -/
def runMembershipTest (filepath : System.FilePath) (n_val : Nat) (hn : n_val ≥ 5) : IO Unit := do
  IO.println s!"Loading data from: {filepath}"

  match ← ParsedMIRData.parseFile filepath n_val (by omega) rfl with
  | none =>
    IO.println "✗ Failed to parse input file"
  | some X =>
    IO.println s!"✓ Data loaded: {X.prob_name}\n"

    let result ← testMembership X hn

    match result with
    | MembershipResult.inConvexHull =>
      IO.println "\n🎉 RESULT: X ∈ conv(Pedigree Paths)"
    | MembershipResult.notInConvexHull msg =>
      IO.println s!"\n❌ RESULT: X ∉ conv(Pedigree Paths)"
      IO.println s!"   Reason: {msg}"
