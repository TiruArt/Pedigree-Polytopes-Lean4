-- MembershipProject/Core/RigidExtraction.lean
-- Frozen flow detection and rigid pedigree extraction from flow networks

import MembershipProject.Core.Types
import MembershipProject.Core.GraphInterface

set_option linter.unusedVariables false

namespace MembershipProject.Core.RigidExtraction

open Core
open GraphInterface

-- ============================================================================
-- PEDIGREE PATH STRUCTURE
-- ============================================================================

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

-- ============================================================================
-- VERTEX MAPPING
-- ============================================================================

/-- Bidirectional mapping between vertex IDs and nodes -/
structure VertexMapping where
  toNode : Nat → Option Node
  fromNode : Node → Option Nat

/-- Build vertex mapping for a layered network

    Convention:
    - Vertex 0: source (if present)
    - Vertices 1..|L_k|: layer k nodes
    - Vertices |L_k|+1..|L_k|+|L_{k+1}|: layer k+1 nodes
    - Vertex (numVertices-1): sink (if present)
-/
def buildLayeredVertexMapping (layerK layerKp1 : List Node) (hasSource hasSink : Bool) : VertexMapping :=
  let sourceOffset := if hasSource then 1 else 0
  let sinkVertex := sourceOffset + layerK.length + layerKp1.length

  let toNodeFn : Nat → Option Node := fun vid =>
    if hasSource && vid = 0 then none  -- Source
    else if hasSink && vid = sinkVertex then none  -- Sink
    else if vid < sourceOffset + layerK.length then
      layerK.get? (vid - sourceOffset)
    else if vid < sourceOffset + layerK.length + layerKp1.length then
      layerKp1.get? (vid - sourceOffset - layerK.length)
    else none

  let fromNodeFn : Node → Option Nat := fun node =>
    -- Find in layerK
    match layerK.findIdx? (· == node) with
    | some idx => some (sourceOffset + idx)
    | none =>
      -- Find in layerKp1
      match layerKp1.findIdx? (· == node) with
      | some idx => some (sourceOffset + layerK.length + idx)
      | none => none

  { toNode := toNodeFn, fromNode := fromNodeFn }

-- ============================================================================
-- CAPACITY CONVERSION
-- ============================================================================

/-- Convert Rat to Int by scaling by 6 and taking numerator -/
def ratToCapacityInt (r : Rat) : Int := (r * 6).num

/-- Convert Int capacity back to Rat by dividing by 6 -/
def capacityIntToRat (i : Int) : Rat := Rat.ofInt i / 6

-- ============================================================================
-- PATH TRACING
-- ============================================================================

/-- Trace a complete pedigree path from a frozen arc

    Given a frozen arc (u,v) with positive flow, trace back to construct
    the complete pedigree path from (1,2,3) to the target node.
-/
def tracePedigreePath (frozenArc : Nat × Nat)
    (flowResult : MaxFlowResult)
    (mapping : VertexMapping)
    (k : Nat) : Option (PedigreePath k) :=
  let (u, v) := frozenArc

  -- Get flow value on this arc (unscale from integer)
  let flowValue := flowResult.flowEdges.toList.find?
    (fun (src, dst, _) => src == u && dst == v)
    |>.map (fun (_, _, f) => capacityIntToRat f)
    |>.getD 0

  if flowValue ≤ 0 then
    none
  else
    match mapping.toNode u, mapping.toNode v with
    | some nodeU, some nodeV =>
      -- Construct path: (1,2,3) → nodeU → nodeV
      -- TODO: Trace complete path back to (1,2,3)
      let path := [
        { i := 1, j := 2, k := 3 : Node },
        nodeU,
        nodeV
      ]
      some { nodes := path, flow := flowValue }
    | _, _ => none

/-- Trace unique path backward from target node through flow network -/
def tracePathBackward (targetNode : Node)
    (flowResult : MaxFlowResult)
    (mapping : VertexMapping) : Option (List Node) :=
  match mapping.fromNode targetNode with
  | none => none
  | some targetVid =>
    -- Find incoming edges with positive flow
    let incomingEdges := flowResult.flowEdges.toList.filter fun (src, dst, flow) =>
      dst == targetVid && flow > 0

    match incomingEdges with
    | [(src, _, _)] =>
      -- Exactly one incoming edge - unique path
      match mapping.toNode src with
      | none => some [targetNode]  -- Reached source
      | some srcNode =>
        if srcNode.k ≤ 3 then
          some [targetNode]  -- Reached base layer
        else
          -- Recursively trace backward
          match tracePathBackward srcNode flowResult mapping with
          | some prevPath => some (prevPath ++ [targetNode])
          | none => none
    | _ => none  -- Not unique (0 or multiple paths)

-- ============================================================================
-- RIGID PEDIGREE EXTRACTION
-- ============================================================================

/-- Extract all rigid pedigrees from frozen flows

    For each frozen arc:
    1. Get flow value
    2. Trace back to construct complete pedigree path
    3. Create PedigreePath with flow value
-/
def extractRigidPedigrees (frozenResult : FrozenFlowsResult)
    (flowResult : MaxFlowResult)
    (mapping : VertexMapping)
    (k : Nat) : List (PedigreePath k) :=
  frozenResult.frozenArcs.toList.filterMap fun arc =>
    tracePedigreePath arc flowResult mapping k

/-- Compute frozen flows and extract rigid pedigrees (main entry point) -/
def computeRigidPedigrees (fn : FlowNetwork)
    (flowResult : MaxFlowResult)
    (mapping : VertexMapping)
    (k : Nat) : IO (List (PedigreePath k)) := do

  IO.println "Computing frozen flows..."
  let frozenResult ← computeFrozenFlows fn flowResult

  IO.println s!"Found {frozenResult.frozenArcs.size} frozen arcs"
  IO.println s!"  Interfaces (between SCCs): {frozenResult.interfaces.size}"
  IO.println s!"  Bridges (within SCCs): {frozenResult.bridges.size}"

  let rigidPedigrees := extractRigidPedigrees frozenResult flowResult mapping k

  IO.println s!"Extracted {rigidPedigrees.length} rigid pedigrees"

  return rigidPedigrees

-- ============================================================================
-- PEDIGREE VALIDATION
-- ============================================================================

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
        -- Check consecutive layers
        let pairs := nodes.zip nodes.tail!
        pairs.all fun (n1, n2) => n2.k = n1.k + 1

/-- Check if extending a pedigree path with a new node is valid -/
def isValidPedigreeExtension (path : PedigreePath k) (newNode : Node) : Bool :=
  if path.nodes.isEmpty then false
  else
    let lastNode := path.nodes.getLast!
    -- Must be consecutive layers
    if newNode.k ≠ lastNode.k + 1 then false
    else
      -- TODO: Add full pedigree constraints
      true

-- ============================================================================
-- DISPLAY AND DEBUGGING
-- ============================================================================

/-- Display a pedigree path -/
def displayPedigreePath {k : Nat} (P : PedigreePath k) : IO Unit := do
  IO.println s!"Pedigree path (flow = {P.flow}):"
  for node in P.nodes do
    IO.println s!"  ({node.i},{node.j},{node.k})"

/-- Display all rigid pedigrees -/
def displayRigidPedigrees {k : Nat} (pedigrees : List (PedigreePath k)) : IO Unit := do
  IO.println s!"Rigid pedigrees: {pedigrees.length}"
  for (idx, P) in pedigrees.enum do
    IO.println s!"Pedigree {idx + 1}:"
    displayPedigreePath P
    IO.println ""

/-- Display summary of rigid pedigrees -/
def displayRigidSummary {k : Nat} (pedigrees : List (PedigreePath k)) : IO Unit := do
  let totalFlow := pedigrees.foldl (fun acc P => acc + P.flow) 0
  IO.println s!"Rigid pedigree summary:"
  IO.println s!"  Count: {pedigrees.length}"
  IO.println s!"  Total rigid flow: {totalFlow}"
  IO.println s!"  Remaining flexible: {1 - totalFlow}"

end MembershipProject.Core.RigidExtraction

-- ============================================================================
-- TESTS AND EXAMPLES
-- ============================================================================

section Examples

open MembershipProject.Core.RigidExtraction

/-- Example: Test pedigree path validation -/
def examplePedigreeValidation : IO Unit := do
  let validPath : List Node := [
    { i := 1, j := 2, k := 3 },
    { i := 1, j := 3, k := 4 },
    { i := 3, j := 4, k := 5 }
  ]

  let invalidPath : List Node := [
    { i := 2, j := 3, k := 3 },  -- Doesn't start at (1,2,3)
    { i := 1, j := 3, k := 4 }
  ]

  IO.println s!"Valid path check: {isValidPedigreePath validPath}"
  IO.println s!"Invalid path check: {isValidPedigreePath invalidPath}"

-- Uncomment to run:
-- #eval examplePedigreeValidation

end Examples
