import Mathlib.Data.Rat.Basic
import Mathlib.Data.List.Basic

namespace F5Network

/-- A node in the F5 network, represented as a pedigree triple (i,j,k) with capacity -/
structure F5Node where
  triple : (Nat × Nat × Nat)
  capacity : Rat
deriving Repr, DecidableEq

/-- An edge in the F5 network with capacity -/
structure F5Edge where
  source : (Nat × Nat × Nat)
  target : (Nat × Nat × Nat)
  capacity : Rat
deriving Repr, DecidableEq

/-- The F5 network structure with 6 layers (0 through 5) -/
structure F5Network where
  layer0 : List F5Node  -- Source layer
  layer1 : List F5Node
  layer2 : List F5Node
  layer3 : List F5Node
  layer4 : List F5Node
  layer5 : List F5Node  -- Sink layer
  edges : List F5Edge
deriving Repr

/-- Helper: Check if two pedigree triples are compatible
    (i,j,k) and (i',j',k') are compatible if:
    - i ≤ i' ≤ j
    - j ≤ j' ≤ k
    - k ≤ k'
-/
def isCompatible (t1 t2 : Nat × Nat × Nat) : Bool :=
  let (i, j, k) := t1
  let (i', j', k') := t2
  i ≤ i' ∧ i' ≤ j ∧ j ≤ j' ∧ j' ≤ k ∧ k ≤ k'

/-- Helper: Get all nodes from a layer -/
def F5Network.getLayer (net : F5Network) (layer : Nat) : List F5Node :=
  match layer with
  | 0 => net.layer0
  | 1 => net.layer1
  | 2 => net.layer2
  | 3 => net.layer3
  | 4 => net.layer4
  | 5 => net.layer5
  | _ => []

/-- Helper: Get all nodes from the network -/
def F5Network.allNodes (net : F5Network) : List F5Node :=
  net.layer0 ++ net.layer1 ++ net.layer2 ++ net.layer3 ++ net.layer4 ++ net.layer5

/-- Helper: Find a node by its triple -/
def F5Network.findNode (net : F5Network) (triple : Nat × Nat × Nat) : Option F5Node :=
  net.allNodes.find? (fun n => n.triple == triple)

/-- Helper: Check if a triple exists in a layer -/
def layerContains (layer : List F5Node) (triple : Nat × Nat × Nat) : Bool :=
  layer.any (fun n => n.triple == triple)

/-- Helper: Get the capacity of a node by its triple -/
def F5Network.getNodeCapacity (net : F5Network) (triple : Nat × Nat × Nat) : Option Rat :=
  match net.findNode triple with
  | none => none
  | some node => some node.capacity

/-- Build edges between two consecutive layers based on compatibility -/
def buildLayerEdges (layer1 layer2 : List F5Node) (edgeCapacity : Rat) : List F5Edge :=
  layer1.foldl (fun acc n1 =>
    let newEdges := layer2.filterMap (fun n2 =>
      if isCompatible n1.triple n2.triple then
        some { source := n1.triple, target := n2.triple, capacity := edgeCapacity }
      else
        none
    )
    acc ++ newEdges
  ) []

/-- Example: Create a simple F5 network for testing -/
def exampleF5Network : F5Network :=
  let source : F5Node := {
    triple := (1, 2, 3)
    capacity := Rat.mk 1 1
  }

  let mid1 : F5Node := {
    triple := (1, 3, 4)
    capacity := Rat.mk 1 2
  }

  let mid2 : F5Node := {
    triple := (2, 3, 4)
    capacity := Rat.mk 1 2
  }

  let sink : F5Node := {
    triple := (2, 4, 5)
    capacity := Rat.mk 1 1
  }

  let edges : List F5Edge := [
    { source := (1, 2, 3), target := (1, 3, 4), capacity := Rat.mk 1 1 },
    { source := (1, 2, 3), target := (2, 3, 4), capacity := Rat.mk 1 1 },
    { source := (1, 3, 4), target := (2, 4, 5), capacity := Rat.mk 1 1 },
    { source := (2, 3, 4), target := (2, 4, 5), capacity := Rat.mk 1 1 }
  ]

  {
    layer0 := [source]
    layer1 := [mid1, mid2]
    layer2 := [sink]
    layer3 := []
    layer4 := []
    layer5 := []
    edges := edges
  }

/-- Verify network structure is valid -/
def F5Network.isValid (net : F5Network) : Bool :=
  -- Check all edges reference existing nodes
  net.edges.all (fun e =>
    let sourceExists := net.allNodes.any (fun n => n.triple == e.source)
    let targetExists := net.allNodes.any (fun n => n.triple == e.target)
    sourceExists ∧ targetExists
  )

/-- Count total number of nodes in network -/
def F5Network.nodeCount (net : F5Network) : Nat :=
  net.layer0.length + net.layer1.length + net.layer2.length +
  net.layer3.length + net.layer4.length + net.layer5.length

/-- Count total number of edges in network -/
def F5Network.edgeCount (net : F5Network) : Nat :=
  net.edges.length

end F5Network
