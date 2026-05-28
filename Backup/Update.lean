-- MembershipProject/Core/NetworkUpdate.lean
-- Network capacity updates and R_k management for M3P algorithm

import MembershipProject.Core.Types
import MembershipProject.Core.GraphInterface
import MembershipProject.Core.RigidExtraction

set_option linter.unusedVariables false

namespace MembershipProject.Core.NetworkUpdate

open Core
open GraphInterface
open RigidExtraction

-- ============================================================================
-- NETWORK CAPACITY UPDATES
-- ============================================================================

/-- Check if an edge corresponds to a node in a pedigree path -/
def edgeMatchesNode (edge : Edge)
    (node : Node)
    (mapping : VertexMapping) : Bool :=
  match mapping.toNode edge.«from», mapping.toNode edge.«to» with
  | some nodeFrom, some nodeTo =>
    (nodeFrom == node) || (nodeTo == node)
  | _, _ => false

/-- Update network by subtracting rigid flows from edge capacities

    For each rigid pedigree P with flow μ(P):
    - Subtract μ(P) from capacity of all edges in P's path

    This produces the updated network N_k for the next stage.
-/
def updateNetworkCapacities (fn : FlowNetwork)
    (rigidPaths : List (PedigreePath k))
    (mapping : VertexMapping) : FlowNetwork :=

  let updatedEdges := rigidPaths.foldl (init := fn.edges) fun edges path =>
    edges.map fun edge =>
      -- Check if edge is part of this path
      let isInPath := path.nodes.any fun node =>
        edgeMatchesNode edge node mapping

      if isInPath then
        -- Subtract flow from capacity
        { edge with capacity := edge.capacity - ratToCapacityInt path.flow }
      else
        edge

  { fn with edges := updatedEdges }

/-- Remove edges with zero or negative capacity -/
def removeZeroCapacityEdges (fn : FlowNetwork) : FlowNetwork :=
  let activeEdges := fn.edges.filter (fun e => e.capacity > 0)
  { fn with edges := activeEdges }

/-- Update network and clean up zero-capacity edges -/
def updateAndCleanNetwork (fn : FlowNetwork)
    (rigidPaths : List (PedigreePath k))
    (mapping : VertexMapping) : FlowNetwork :=
  let updated := updateNetworkCapacities fn rigidPaths mapping
  removeZeroCapacityEdges updated

-- ============================================================================
-- R_k MANAGEMENT
-- ============================================================================

/-- Find which R_k pedigrees extend which R_{k-1} pedigrees

    Returns: List of (P_{k-1}, flow_extended) pairs
-/
def findExtensions (R_prev : List (PedigreePath (k-1)))
    (R_k : List (PedigreePath k)) : List (PedigreePath (k-1) × Rat) :=
  R_k.filterMap fun Pk =>
    -- Check if Pk extends some P in R_prev
    -- A pedigree Pk extends P if the first k-1 nodes of Pk match P's nodes
    R_prev.find? fun P =>
      -- Compare first (k-1) nodes
      Pk.nodes.take (k-1) == P.nodes
    |>.map fun P => (P, Pk.flow)

/-- Update R_{k-1} by subtracting flows that were extended to R_k

    For each P in R_{k-1}:
    - If P was extended by pedigrees in R_k, subtract those flows
    - If P still has positive capacity, keep it in updated R_{k-1}
    - Otherwise, remove it (fully consumed)

    Returns: (updated R_{k-1}, updated μ_{k-1})
-/
def updateRprev (R_prev : List (PedigreePath (k-1)))
    (μ_prev : PedigreePath (k-1) → Rat)
    (R_k : List (PedigreePath k)) :
    (List (PedigreePath (k-1)) × (PedigreePath (k-1) → Rat)) :=

  -- Find all extensions
  let extensionFlows := findExtensions R_prev R_k

  -- Update R_{k-1}: keep only pedigrees with remaining capacity
  let updatedRprev := R_prev.filterMap fun P =>
    let totalExtended := extensionFlows.filter (fun (P', _) => P' == P)
                                       .foldl (fun acc (_, flow) => acc + flow) 0
    let newCapacity := μ_prev P - totalExtended
    if newCapacity > 0 then
      some P
    else
      none

  -- Update μ_{k-1}
  let updatedμ := fun (P : PedigreePath (k-1)) =>
    let totalExtended := extensionFlows.filter (fun (P', _) => P' == P)
                                       .foldl (fun acc (_, flow) => acc + flow) 0
    μ_prev P - totalExtended

  (updatedRprev, updatedμ)

-- ============================================================================
-- FLEXIBLE FLOW TRACKING
-- ============================================================================

/-- Compute Z_max: maximum flexible flow remaining

    Z_max = 1 - (total rigid flow at stage k)

    Termination condition: Z_max = 0 means all flow is rigid
-/
def computeZmax (R_k : List (PedigreePath k)) : Rat :=
  let totalRigid := R_k.foldl (init := 0) (fun acc P => acc + P.flow)
  1 - totalRigid

/-- Check if all flow is rigid (termination condition) -/
def isFullyRigid (R_k : List (PedigreePath k)) : Bool :=
  computeZmax R_k == 0

/-- Check if there is still flexible flow -/
def hasFlexibleFlow (R_k : List (PedigreePath k)) : Bool :=
  computeZmax R_k > 0

-- ============================================================================
-- FLOW ACCOUNTING
-- ============================================================================

/-- Structure to track flow distribution -/
structure FlowAccounting (k : ℕ) where
  totalFlow : Rat
  rigidFlow : Rat
  flexibleFlow : Rat
  numRigidPedigrees : Nat
  deriving Repr

/-- Compute flow accounting for stage k -/
def computeFlowAccounting (R_k : List (PedigreePath k)) : FlowAccounting k :=
  let rigidFlow := R_k.foldl (fun acc P => acc + P.flow) 0
  { totalFlow := 1,
    rigidFlow := rigidFlow,
    flexibleFlow := 1 - rigidFlow,
    numRigidPedigrees := R_k.length }

/-- Display flow accounting -/
def displayFlowAccounting {k : Nat} (acc : FlowAccounting k) (stage : Nat) : IO Unit := do
  IO.println s!"Flow accounting at stage {stage}:"
  IO.println s!"  Total flow: {acc.totalFlow}"
  IO.println s!"  Rigid flow: {acc.rigidFlow}"
  IO.println s!"  Flexible flow: {acc.flexibleFlow}"
  IO.println s!"  Rigid pedigrees: {acc.numRigidPedigrees}"
  if acc.flexibleFlow == 0 then
    IO.println "  ✓ All flow is rigid!"

-- ============================================================================
-- VALIDATION
-- ============================================================================

/-- Validate that flow is conserved after updates -/
def validateFlowConservation (R_prev : List (PedigreePath (k-1)))
    (μ_prev : PedigreePath (k-1) → Rat)
    (R_k : List (PedigreePath k))
    (R_prev_updated : List (PedigreePath (k-1)))
    (μ_prev_updated : PedigreePath (k-1) → Rat) : Bool :=

  let totalBefore := R_prev.foldl (fun acc P => acc + μ_prev P) 0
  let totalAfter := R_prev_updated.foldl (fun acc P => acc + μ_prev_updated P) 0 +
                    R_k.foldl (fun acc P => acc + P.flow) 0

  -- Should be equal (allowing for small numerical errors)
  abs (totalBefore - totalAfter) < 0.0001

/-- Check if R_{k-1} update is valid -/
def isValidRprevUpdate (R_prev : List (PedigreePath (k-1)))
    (μ_prev : PedigreePath (k-1) → Rat)
    (R_k : List (PedigreePath k))
    (R_prev_updated : List (PedigreePath (k-1)))
    (μ_prev_updated : PedigreePath (k-1) → Rat) : IO Bool := do

  let flowConserved := validateFlowConservation R_prev μ_prev R_k R_prev_updated μ_prev_updated

  if not flowConserved then
    IO.println "⚠ Warning: Flow conservation violated in R_{k-1} update!"
    return false

  -- Check non-negativity
  for P in R_prev_updated do
    if μ_prev_updated P < 0 then
      IO.println s!"⚠ Warning: Negative capacity in updated R_{{k-1}}: {μ_prev_updated P}"
      return false

  return true

-- ============================================================================
-- DISPLAY FUNCTIONS
-- ============================================================================

/-- Display R_{k-1} update summary -/
def displayRprevUpdate {k : Nat}
    (R_prev : List (PedigreePath (k-1)))
    (R_prev_updated : List (PedigreePath (k-1)))
    (stage : Nat) : IO Unit := do

  let numRemoved := R_prev.length - R_prev_updated.length

  IO.println s!"R_{{{stage-1}}} update:"
  IO.println s!"  Before: {R_prev.length} pedigrees"
  IO.println s!"  After: {R_prev_updated.length} pedigrees"
  IO.println s!"  Removed: {numRemoved} (fully extended)"

/-- Display network update summary -/
def displayNetworkUpdate (fn_before fn_after : FlowNetwork) (stage : Nat) : IO Unit := do
  let edgesBefore := fn_before.edges.size
  let edgesAfter := fn_after.edges.size
  let edgesRemoved := edgesBefore - edgesAfter

  IO.println s!"N_{stage} update:"
  IO.println s!"  Edges before: {edgesBefore}"
  IO.println s!"  Edges after: {edgesAfter}"
  IO.println s!"  Zero-capacity edges removed: {edgesRemoved}"

end MembershipProject.Core.NetworkUpdate

-- ============================================================================
-- TESTS AND EXAMPLES
-- ============================================================================

section Examples

open MembershipProject.Core.NetworkUpdate

/-- Example: Test Z_max computation -/
def exampleZmax : IO Unit := do
  let R4 : List (PedigreePath 4) := [
    { nodes := [], flow := 0.3 },
    { nodes := [], flow := 0.5 }
  ]

  let zmax := computeZmax R4
  IO.println s!"Example: Total rigid = 0.8, Z_max = {zmax}"
  IO.println s!"Fully rigid? {isFullyRigid R4}"
  IO.println s!"Has flexible flow? {hasFlexibleFlow R4}"

-- Uncomment to run:
-- #eval exampleZmax

end Examples
