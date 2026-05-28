-- ArcRules.lean
import MembershipProject.Core.Types

namespace MembershipProject.Core

-- ============================================
-- LAYER AND NODE MANAGEMENT
-- ============================================

/-- Get all nodes in a given layer k -/
def nodesInLayer (k : Nat) : List Node :=
  if k < 3 then []
  else
    (List.range (k - 1)).flatMap fun i =>
      (List.range (k - 1)).filterMap fun j =>
        if i < j && j < k - 1 then
          some { i := i + 1, j := j + 1, k := k : Node }
        else none

/-- Get all potential arcs between layer k and k+1 -/
def allArcsBetweenLayers (k : Nat) : List (Node × Node) :=
  let layerK := nodesInLayer k
  let layerKp1 := nodesInLayer (k + 1)
  layerK.flatMap fun src =>
    layerKp1.map fun tgt => (src, tgt)

-- ============================================
-- F₄ FORBIDDEN ARC RULES
-- ============================================

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
def permittedArcsForStage (k : Nat) : List (Node × Node) :=
  let allArcs := allArcsBetweenLayers k
  allArcs.filter fun (src, tgt) =>
    isPermittedArcForLayer src tgt

-- ============================================
-- EXTENDED ARC RULES FOR k ≥ 5
-- ============================================

/-- Check if arc from layer k to k+1 is permitted for k ≥ 5
    Rule: An arc (i,j,k) → (i',j',k+1) is permitted if:
    - Either i' ∈ {i,j} OR j' ∈ {i,j}
    - This ensures the new node shares at least one index with the previous node -/
def isPermittedArcGeneral (srcNode tgtNode : Node) : Bool :=
  if srcNode.k + 1 ≠ tgtNode.k then false
  else
    match srcNode.k with
    | 3 => true  -- Layer 3→4: all arcs permitted
    | 4 => isPermittedArc45 srcNode tgtNode  -- Layer 4→5: special F₄ rules
    | _ =>  -- Layer k→k+1 for k ≥ 5
      -- At least one index must be shared
      (tgtNode.i = srcNode.i) || (tgtNode.i = srcNode.j) ||
      (tgtNode.j = srcNode.i) || (tgtNode.j = srcNode.j)

/-- Check if extending a path with a new node maintains pedigree validity -/
def isValidPedigreeExtension (prevNode newNode : Node) : Bool :=
  -- Must go to next layer
  if newNode.k ≠ prevNode.k + 1 then false
  else
    -- Use general arc rules
    isPermittedArcGeneral prevNode newNode

/-- Check if a node in layer k+1 can extend any rigid pedigree from R_k -/
def canExtendAnyRigidPedigree (rigidPaths : List Node) (targetNode : Node) : Bool :=
  rigidPaths.any fun srcNode =>
    isValidPedigreeExtension srcNode targetNode

/-- Get all nodes in layer k that can reach a node in layer k+1
    Used for F_k bipartite matching construction -/
def getSourceNodesForTarget (k : Nat) (targetNode : Node) : List Node :=
  let layerK := nodesInLayer k
  layerK.filter fun srcNode =>
    isPermittedArcGeneral srcNode targetNode

/-- Get all nodes in layer k+1 reachable from a node in layer k
    Used for arc capacity computation -/
def getTargetNodesFromSource (k : Nat) (srcNode : Node) : List Node :=
  let layerKp1 := nodesInLayer (k + 1)
  layerKp1.filter fun tgtNode =>
    isPermittedArcGeneral srcNode tgtNode

/-- Check if there exists a valid path from layer k-1 to layer k+1 through layer k
    This is used to determine if an arc should be included in F_k -/
def hasValidPathThrough (layerKm1Node : Node) (layerKNode : Node) (layerKp1Node : Node) : Bool :=
  isPermittedArcGeneral layerKm1Node layerKNode &&
  isPermittedArcGeneral layerKNode layerKp1Node

/-- Get all valid "transit nodes" in layer k that can connect layer k-1 to layer k+1 -/
def getTransitNodes (k : Nat) (sourceNode : Node) (targetNode : Node) : List Node :=
  let layerK := nodesInLayer k
  layerK.filter fun transitNode =>
    hasValidPathThrough sourceNode transitNode targetNode

end MembershipProject.Core
