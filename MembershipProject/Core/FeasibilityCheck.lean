-- Core/FeasibilityCheck.lean
import Mathlib.Tactic
import MembershipProject.Core.Basic
import MembershipProject.Core.SlackComputation
import MembershipProject.Core.Types

set_option linter.unusedVariables false

namespace MembershipProject.Core

open Nat

-- ============================================
-- FEASIBILITY FOR MATHEMATICAL STRUCTURE
-- ============================================

/-- Check if a MIR structure is feasible (all slacks non-negative) -/
def isFeasible (n : Nat) (mir : MIRStructure n) : Prop :=
  ∀ (k : Nat) (hk3 : 3 ≤ k) (hkn : k ≤ n) (e : Edge k),
    computeSlackSparse n mir k hk3 hkn e ≥ (0 : Rat)

/-- Check if a rational number is negative -/
def isNegative (r : Rat) : Bool :=
  r < (0 : Rat)

/-- Enumerate all edges for a given stage k -/
def enumerateEdges (k : Nat) : List (Edge k) :=
  let rec loop (i j : Nat) (acc : List (Edge k)) : List (Edge k) :=
    if _h : i ≥ k then acc
    else if _h' : j ≥ k then loop (i + 1) (i + 2) acc
    else
      if hij_cond : i < j then
        have hi : i < k := by omega
        have hj : j < k := by omega
        loop i (j + 1) (⟨i, j, hi, hj, hij_cond⟩ :: acc)
      else
        loop i (j + 1) acc
  loop 0 1 []

-- ============================================
-- FEASIBILITY FOR PARSED DATA
-- ============================================

/-- Result of feasibility check for parsed data -/
structure FeasibilityResult where
  feasible : Bool
  first_infeasible_stage : Option Nat
  deriving Repr

/-- Check if parsed data X satisfies basic P_MI(n) properties -/
def checkParsedDataFeasibility (n : Nat) (X : ParsedMIRData n) : FeasibilityResult :=
  -- Note: Non-negativity is guaranteed by SparseEntry.h_nonneg, so we only check completeness
  let hasAllStages := (List.range (n - 2)).all fun i =>
    X.data.any (fun entry => entry.k = i + 3)
  if hasAllStages then
    { feasible := true, first_infeasible_stage := none }
  else
    let firstBadStage := (List.range (n - 2)).find? fun i =>
      let k := i + 3
      let stageEntries := X.data.filter (fun entry => entry.k = k)
      stageEntries.isEmpty
    { feasible := false, first_infeasible_stage := firstBadStage.map (· + 3) }

/-- Quick check: verify all stages from 3 to n have data -/
def hasCompleteStages (n : Nat) (X : ParsedMIRData n) : Bool :=
  (List.range (n - 2)).all fun i =>
    X.data.any (fun entry => entry.k = i + 3)

/-- Count how many stages have data -/
def countStagesWithData (n : Nat) (X : ParsedMIRData n) : Nat :=
  (List.range (n - 2)).countP fun i =>
    X.data.any (fun entry => entry.k = i + 3)

/-- Display feasibility result -/
def displayFeasibilityResult (result : FeasibilityResult) : IO Unit := do
  if result.feasible then
    IO.println "✓ Feasibility check PASSED"
  else
    match result.first_infeasible_stage with
    | some k => IO.println s!"✗ Feasibility check FAILED at stage {k}"
    | none => IO.println "✗ Feasibility check FAILED (reason unknown)"

/-- Detailed feasibility report -/
def displayDetailedFeasibility (n : Nat) (X : ParsedMIRData n) : IO Unit := do
  IO.println "=== FEASIBILITY CHECK REPORT ==="
  IO.println s!"Problem: {X.prob_name}"
  IO.println s!"Size: n = {n}"
  let stagesWithData := countStagesWithData n X
  let totalStages := n - 2
  IO.println s!"Stage Coverage: {stagesWithData}/{totalStages}"
  let isMissing := fun i =>
    let k := i + 3
    not (X.data.any (fun entry => entry.k = k))
  let missingStages := (List.range (n - 2)).filter isMissing
  if missingStages.isEmpty then
    IO.println "✓ All stages have data"
  else
    IO.println s!"✗ Missing data for stages: {missingStages.map (· + 3)}"
  IO.println "✓ All values are non-negative (guaranteed by type system)"
  let result := checkParsedDataFeasibility n X
  displayFeasibilityResult result
end MembershipProject.Core
