-- PedigreeProject/Core/DataParser.lean
-- Data Parsing and Access Module for SparseRecursiveMIR
-- FORMAT: k values first (Line 3), then (i,j) pairs (Line 4), then x values (Line 5)

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import MembershipProject.Core.Types

set_option linter.unusedVariables false
set_option linter.style.emptyLine false

/-!
# SparseRecursiveMIR Data Structure and Parsing

## PURPOSE:
Parse and access pedigree polytope membership data where:
- x_k vectors give node capacities for layer k
- Node (i,j,k) has capacity/availability p(i,j,k) = x_ij^k

## INPUT FORMAT (k-first):
```
Line 1: Problem name (String)
Line 2: n (Nat) - number of cities
Line 3: k values (stages) - organized by stage
Line 4: (i,j) edges corresponding to each k
Line 5: x_ijk values (node capacities)
Line 6: Optional PMI status (True/False/empty)
```

## EXAMPLE:
```
Example_Problem_7
7
4    4    5    6    6    7    7    7
1,3  2,3  3,4  1,2  3,5  3,5  4,5  5,6
0.5  0.5  1.0  0.5  0.5  0.25 0.5  0.25
True
```
-/

namespace MembershipProject.Core

def parseEdgePair (s : String) : Option (Nat × Nat) := do
  let parts := s.splitOn ","
  guard (parts.length = 2)
  let i ← parts[0]?.bind String.toNat?
  let j ← parts[1]?.bind String.toNat?
  guard (i < j)
  return (i, j)

/-- Parse a rational number from string (handles integers and decimals) -/
def parseRational (s : String) : Option Rat := do
  -- Try parsing as integer first
  if let some n := s.toNat? then
    return Rat.ofInt n
  -- Try parsing as decimal
  let parts := s.splitOn "."
  guard (parts.length ≤ 2)
  let wholePart ← parts[0]?.bind String.toNat?
  if parts.length = 1 then
    return Rat.ofInt wholePart
  else
    let fracPart ← parts[1]?.bind String.toNat?
    let fracStr := parts[1]?.getD ""
    let denominator := 10 ^ fracStr.length
    return Rat.divInt (wholePart * denominator + fracPart) denominator

namespace ParsedMIRData

/-- Parse complete ParsedMIRData from list of strings -/
def parse {n : ℕ} (lines : List String) (n_val : ℕ) (hn : n_val ≥ 3) (heq : n = n_val) :
    Option (ParsedMIRData n) := do
  guard (lines.length ≥ 5)
  -- Line 1: Problem name
  let prob_name := lines[0]?.getD "unnamed_problem"
  -- Line 2: n (verify it matches the parameter)
  let n_str ← lines[1]?
  let n_parsed ← n_str.trimAscii.toString.toNat?
  guard (n_parsed = n_val)
  -- Line 3: k values (FIRST in k-first format)
  let k_str := lines[2]?.getD ""
  let k_strs := k_str.splitOn " " |>.filter (· ≠ "")
  let k_vals ← k_strs.mapM String.toNat?
  -- Line 4: Edges (SECOND in k-first format)
  let edges_str := lines[3]?.getD ""
  let edge_strs := edges_str.splitOn " " |>.filter (· ≠ "")
  let edges ← edge_strs.mapM parseEdgePair
  -- Line 5: x_ijk values (node capacities)
  let val_str := lines[4]?.getD ""
  let val_strs := val_str.splitOn " " |>.filter (· ≠ "")
  let values ← val_strs.mapM parseRational
  -- Verify all arrays have same length
  guard (k_vals.length = edges.length ∧ edges.length = values.length)
  -- Build entries array
  let entries_list := List.zipWith3
    (fun (k : Nat) (edge : Nat × Nat) (val : Rat) =>
      -- Valid constraints: 1 ≤ i < j < k ≤ n AND val ≥ 0
      if hk : k ≤ n then
        if hi : edge.1 < n then
          if hi_pos : 1 ≤ edge.1 then
            if hj : edge.2 < n then
              if h_ord : edge.1 < edge.2 then
                if h_jk : edge.2 < k then
                  if h_nonneg : val ≥ 0 then
                    some { i := ⟨edge.1, hi⟩
                         , j := ⟨edge.2, hj⟩
                         , k := k
                         , value := val
                         , h_order := h_ord
                         , h_i_bound := hi_pos
                         , h_j_less_k := h_jk
                         , h_k_bound := hk
                         , h_nonneg := h_nonneg : SparseEntry n }
                  else none
                else none
              else none
            else none
          else none
        else none
      else none)
    k_vals edges values

  let entries := entries_list.filterMap id |>.toArray
  -- Line 6: Optional PMI status
  let pmi_status :=
    if lines.length > 5 then
      match lines[5]?.map (·.trimAscii.toString) with
      | some "True" => some true
      | some "False" => some false
      | _ => none
    else none

  return { prob_name := prob_name
         , data := entries
         , pmi_status := pmi_status }

/-- Parse from a single multiline string -/
def parseString {n : ℕ} (input : String) (n_val : ℕ) (hn : n_val ≥ 3) (heq : n = n_val) :
    Option (ParsedMIRData n) :=
  let lines := input.splitOn "\n" |>.map (·.trimAscii.toString)
  parse lines n_val hn heq

/-- Parse from file path -/
def parseFile {n : ℕ} (path : System.FilePath) (n_val : ℕ) (hn : n_val ≥ 3) (heq : n = n_val) :
    IO (Option (ParsedMIRData n)) := do
  let content ← IO.FS.readFile path
  return parseString content n_val hn heq

/-- Get value x_{ij}^k from sparse data (returns 0 if not found) -/
def getValue {n : ℕ} (X : ParsedMIRData n) (i j k : Nat) : Rat :=
  let (i', j') := if i < j then (i, j) else (j, i)
  X.data.find? (fun entry =>
    entry.i.val = i' ∧ entry.j.val = j' ∧ entry.k = k
  ) |>.map (·.value) |>.getD (0 : Rat)

/-- Get value x_{ij}^k with Fin indices -/
def getValueFin {n : ℕ} (X : ParsedMIRData n) (i j k : Fin n) : Rat :=
  getValue X i.val j.val k.val

/-- Get all entries for a specific stage k -/
def getStageEntries {n : ℕ} (X : ParsedMIRData n) (k : Nat) :
    Array (SparseEntry n) :=
  X.data.filter (·.k = k)

/-- Get all entries for a specific stage k (Fin version) -/
def getStageEntriesFin {n : ℕ} (X : ParsedMIRData n) (k : Fin n) :
    Array (SparseEntry n) :=
  X.data.filter (·.k = k.val)

/-- Get total availability at stage k -/
def getTotalAvailability {n : ℕ} (X : ParsedMIRData n) (k : Nat) : Rat :=
  let stageData := getStageEntries X k
  stageData.foldl (fun acc entry => acc + entry.value) (0 : Rat)

/-- Get total demand at stage k -/
def getTotalDemand {n : ℕ} (X : ParsedMIRData n) (k : Nat) : Rat :=
  getTotalAvailability X k

/-- Get all entries for a specific edge (i,j) across all stages -/
def getEdgeEntries {n : ℕ} (X : ParsedMIRData n) (i j : Nat) :
    Array (SparseEntry n) :=
  let (i', j') := if i < j then (i, j) else (j, i)
  X.data.filter (fun entry => entry.i.val = i' ∧ entry.j.val = j')

/-- Check if data exists for stage k -/
def hasStageData {n : ℕ} (X : ParsedMIRData n) (k : Nat) : Bool :=
  X.data.any (·.k = k)

/-- Get all stages that have data -/
def getAvailableStages {n : ℕ} (X : ParsedMIRData n) : List Nat :=
  let stages := X.data.map (·.k) |>.toList
  stages.eraseDups.toArray.qsort (· < ·) |>.toList

/-- Get total number of entries -/
def numEntries {n : ℕ} (X : ParsedMIRData n) : Nat :=
  X.data.size

/-- Validate that data has entries for all required stages (3 through n) -/
def isComplete {n : ℕ} (X : ParsedMIRData n) : Bool :=
  let stages := getAvailableStages X
  (List.range (n - 2)).all (fun i => (i + 3) ∈ stages)

/-- Get summary statistics about the data -/
structure DataSummary where
  num_entries : Nat
  stages_present : List Nat
  min_stage : Option Nat
  max_stage : Option Nat
  is_complete : Bool
  deriving Repr

def getSummary {n : ℕ} (X : ParsedMIRData n) : DataSummary :=
  let stages := getAvailableStages X
  { num_entries := X.data.size
  , stages_present := stages
  , min_stage := stages.head?
  , max_stage := stages.getLast?
  , is_complete := isComplete X }

/-- Pretty print the data structure -/
def toString {n : ℕ} (X : ParsedMIRData n) : String :=
  let summary := getSummary X
  let pmi_str := match X.pmi_status with
    | some true => "✓ (verified)"
    | some false => "✗ (rejected)"
    | none => "? (not checked)"
  s!"Problem: {X.prob_name}\n" ++
  s!"Size: n = {n}\n" ++
  s!"Entries: {summary.num_entries}\n" ++
  s!"Stages: {summary.stages_present}\n" ++
  s!"Complete: {summary.is_complete}\n" ++
  s!"P_MI status: {pmi_str}"

instance {n : ℕ} : ToString (ParsedMIRData n) where
  toString := toString

/-- Display x_k vector for a given stage k -/
def displayStageVector {n : ℕ} (X : ParsedMIRData n) (k : Nat) : IO Unit := do
  let entries := getStageEntries X k
  if entries.size = 0 then
    IO.println s!"x_{k} has no non-zero entries (all zeros)"
  else
    IO.println s!"x_{k} non-zero entries:"
    for entry in entries.toList do
      IO.println s!"  ({entry.i.val},{entry.j.val},{entry.k}) = {entry.value}"

end ParsedMIRData

end MembershipProject.Core

/-!
## USAGE EXAMPLES
-/

section Examples

open MembershipProject.Core

/-- Example: Parse the given data -/
def exampleParse : IO Unit := do
  let input := [
    "Example_Problem_7",
    "7",
    "4    4    5    6    6    7    7    7",
    "1,3  2,3  3,4  1,2  3,5  3,5  4,5  5,6",
    "0.5  0.5  1.0  0.5  0.5  0.25 0.5  0.25",
    ""
  ]

  match ParsedMIRData.parse input 7 (by omega) rfl with
  | none => IO.println "❌ Parse failed"
  | some X => do
      IO.println s!"✅ {X}\n"
      -- Show stage vectors
      IO.println "Stage Vectors:"
      for k in [4, 5, 6, 7] do
        ParsedMIRData.displayStageVector X k
        IO.println ""
      -- Show totals for F_4
      IO.println "For F_4 (Layer 4 → Layer 5):"
      let avail := ParsedMIRData.getTotalAvailability X 4
      let demand := ParsedMIRData.getTotalDemand X 5
      IO.println s!"  Layer 4 total availability: {avail}"
      IO.println s!"  Layer 5 total demand: {demand}"

-- Uncomment to run the example:
-- #eval exampleParse

end Examples
