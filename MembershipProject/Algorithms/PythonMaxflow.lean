import Lean
import Lean.Data.Json
import MembershipProject.Core.F5Network

namespace MembershipProject.Algorithms

open Lean (Json toJson fromJson?)
open F5Network

/-- JSON representation of a node with capacity and layer -/
structure NodeJson where
  node : (Nat × Nat × Nat)
  capacity : String
  layer : Nat
deriving Lean.ToJson, Lean.FromJson

/-- JSON representation of an edge with capacity -/
structure EdgeJson where
  source : (Nat × Nat × Nat)
  target : (Nat × Nat × Nat)
  capacity : String
deriving Lean.ToJson, Lean.FromJson

/-- JSON input for Python max-flow computation -/
structure MaxFlowInput where
  nodes : List NodeJson
  edges : List EdgeJson
  source : (Nat × Nat × Nat)
  sink : (Nat × Nat × Nat)
deriving Lean.ToJson, Lean.FromJson

/-- JSON output from Python max-flow computation -/
structure MaxFlowOutput where
  maxFlow : String  -- "numerator/denominator"
  success : Bool
  error : Option String
deriving Lean.ToJson, Lean.FromJson

/-- Convert Rat to string in "numerator/denominator" format -/
def ratToString (r : Rat) : String :=
  s!"{r.num}/{r.den}"

/-- Parse string "numerator/denominator" to Rat -/
def stringToRat (s : String) : Option Rat := do
  let parts := s.splitOn "/"
  guard (parts.length == 2)
  let num ← parts[0]?.bind String.toInt?
  let den ← parts[1]?.bind String.toNat?
  guard (den > 0)
  return Rat.mk num den

/-- Convert F5Network edge to JSON format -/
def edgeToJson (e : F5Edge) : EdgeJson :=
  { source := e.source
    target := e.target
    capacity := ratToString e.capacity }

/-- Convert F5Network node to JSON format -/
def nodeToJson (n : F5Node) (layer : Nat) : NodeJson :=
  { node := n.triple
    capacity := ratToString n.capacity
    layer := layer }

/-- Build list of all nodes with their layers from F5Network -/
def collectNodesWithLayers (net : F5Network) : List NodeJson :=
  let layer0 := net.layer0.map (fun n => nodeToJson n 0)
  let layer1 := net.layer1.map (fun n => nodeToJson n 1)
  let layer2 := net.layer2.map (fun n => nodeToJson n 2)
  let layer3 := net.layer3.map (fun n => nodeToJson n 3)
  let layer4 := net.layer4.map (fun n => nodeToJson n 4)
  let layer5 := net.layer5.map (fun n => nodeToJson n 5)
  layer0 ++ layer1 ++ layer2 ++ layer3 ++ layer4 ++ layer5

/-- Prepare input for Python max-flow computation -/
def prepareMaxFlowInput (net : F5Network) (source sink : (Nat × Nat × Nat)) : MaxFlowInput :=
  { nodes := collectNodesWithLayers net
    edges := net.edges.map edgeToJson
    source := source
    sink := sink }

/-- Call Python max-flow script and parse result -/
def callPythonMaxFlow (input : MaxFlowInput) : IO MaxFlowOutput := do
  -- Serialize input to JSON
  let inputJson := toJson input
  let inputStr := inputJson.compress

  -- Write to temporary file
  let tmpInput := "/tmp/maxflow_input.json"
  let tmpOutput := "/tmp/maxflow_output.json"
  IO.FS.writeFile tmpInput inputStr

  -- Call Python script
  -- Adjust path to your Python script location
  let pythonScript := "MembershipProject/Algorithms/maxflow_wrapper.py"
  let cmd := "python3"
  let args := #[pythonScript, tmpInput, tmpOutput]

  let output ← IO.Process.run { cmd := cmd, args := args }

  -- Check if Python script succeeded
  if output.trim != "SUCCESS" then
    return { maxFlow := "0/1", success := false, error := some output }

  -- Read output file
  let outputStr ← IO.FS.readFile tmpOutput

  -- Parse JSON output
  match Json.parse outputStr with
  | Except.error e =>
      return { maxFlow := "0/1", success := false, error := some s!"JSON parse error: {e}" }
  | Except.ok json =>
      match fromJson? json with
      | Except.error e =>
          return { maxFlow := "0/1", success := false, error := some s!"JSON decode error: {e}" }
      | Except.ok result => return result

/-- Main function: compute max-flow for F5Network -/
def computeF5MaxFlow (net : F5Network) (source sink : (Nat × Nat × Nat)) : IO (Option Rat) := do
  let input := prepareMaxFlowInput net source sink
  let output ← callPythonMaxFlow input

  if !output.success then
    IO.eprintln s!"Max-flow computation failed: {output.error.getD "Unknown error"}"
    return none

  match stringToRat output.maxFlow with
  | none =>
      IO.eprintln s!"Failed to parse max-flow result: {output.maxFlow}"
      return none
  | some flow => return some flow

/-- Check if point is in pedigree polytope using max-flow -/
def checkPolytopeMembership (net : F5Network) (source sink : (Nat × Nat × Nat)) : IO Bool := do
  match ← computeF5MaxFlow net source sink with
  | none => return false
  | some flow =>
      -- Point is in polytope if max-flow equals source capacity
      let sourceNode := net.layer0.find? (fun n => n.triple == source)
      match sourceNode with
      | none => return false
      | some sn => return flow == sn.capacity

end MembershipProject.Algorithms
