-- DataParserTest.lean
-- Comprehensive test to verify Book_problem data parsing

import MembershipProject.Core.DataParser
import MembershipProject.Core.Types

open MembershipProject.Core

/-- Parse the alignment from the input to show expected structure -/
def showExpectedStructure : IO Unit := do
  IO.println "=== EXPECTED DATA STRUCTURE (from visual alignment) ==="
  IO.println ""
  IO.println "Entry | (i,j) | k  | Value | Notes"
  IO.println "------|-------|----|----|----------------------------------"
  IO.println "  1   | (1,2) | 4  | 1.00 | "
  IO.println "  2   | (1,3) | 5  | 0.75 | "
  IO.println "  3   | (1,4) | 5  | 0.25 | Multiple entries at k=5"
  IO.println "  4   | (2,4) | 6  | 0.50 | "
  IO.println "  5   | (3,5) | 6  | 0.25 | "
  IO.println "  6   | (4,5) | 6  | 0.25 | Multiple entries at k=6"
  IO.println "  7   | (2,3) | 7  | 0.25 | "
  IO.println "  8   | (1,5) | 7  | 0.25 | "
  IO.println "  9   | (4,6) | 7  | 0.25 | "
  IO.println " 10   | (5,6) | 7  | 0.25 | Multiple entries at k=7"
  IO.println " 11   | (2,3) | 8  | 0.25 | DUPLICATE pair (2,3), different k"
  IO.println " 12   | (1,4) | 8  | 0.50 | DUPLICATE pair (1,4), different k"
  IO.println " 13   | (4,6) | 8  | 0.25 | DUPLICATE pair (4,6), different k"
  IO.println " 14   | (2,6) | 9  | 0.50 | "
  IO.println " 15   | (1,8) | 9  | 0.25 | "
  IO.println " 16   | (6,8) | 9  | 0.25 | "
  IO.println " 17   | (3,5) | 10 | 0.50 | DUPLICATE pair (3,5), different k"
  IO.println " 18   | (4,7) | 10 | 0.25 | "
  IO.println " 19   | (6,7) | 10 | 0.25 | "
  IO.println ""

/-- Verify and display parsed data structure -/
def verifyBookProblemData {n : ℕ} (filePath : String) : IO Unit := do
  IO.println "╔════════════════════════════════════════════════╗"
  IO.println "║     Book_problem Data Parser Verification     ║"
  IO.println "╚════════════════════════════════════════════════╝"
  IO.println ""

  -- Show what we expect first
  showExpectedStructure

  -- Parse the file
  IO.println "=== PARSING FILE ==="
  IO.println s!"Reading file: {filePath}"
  let parseResult ← parseInputFile filePath

  match parseResult with
  | Except.error msg =>
    IO.println s!"✗ ERROR: {msg}"
  | Except.ok (data : ParsedMIRData n) =>
    IO.println "✓ File parsed successfully"
    IO.println ""

    -- Display basic information
    IO.println "=== PARSED DATA SUMMARY ==="
    IO.println s!"Problem name: {data.prob_name}"
    IO.println s!"n = {n}"
    IO.println s!"Number of entries: {data.data.size}"
    IO.println s!"PMI status: {data.pmi_status}"
    IO.println ""

    -- Display all entries in order
    IO.println "=== ALL PARSED ENTRIES (in order) ==="
    IO.println "Entry | (i,j) | k  | Value | Status"
    IO.println "------|-------|----|----|----------------------------------"

    for idx in List.range data.data.size do
      let entry := data.data.get! idx
      let status :=
        if idx < 19 then "✓"
        else "⚠ Extra entry?"
      IO.println s!" {idx+1:3}   | ({entry.i.val},{entry.j.val}) | {entry.k:2} | {entry.value} | {status}"

    if data.data.size < 19 then
      IO.println s!"\n⚠ WARNING: Only {data.data.size} entries found, expected 19"
    else if data.data.size > 19 then
      IO.println s!"\n⚠ WARNING: {data.data.size} entries found, expected 19"
    else
      IO.println "\n✓ Correct number of entries (19)"

    IO.println ""

    -- Group entries by k value
    IO.println "=== ENTRIES GROUPED BY k VALUE ==="
    for k in [4, 5, 6, 7, 8, 9, 10] do
      let entriesAtK := data.data.toList.filter (fun e => e.k = k)
      if entriesAtK.length > 0 then
        IO.println s!"\nLayer k={k}: {entriesAtK.length} entries"
        for entry in entriesAtK do
          IO.println s!"  ({entry.i.val},{entry.j.val}) = {entry.value}"

    IO.println ""
    IO.println "=== SPOT CHECKS ==="

    -- Define test cases with Rat values
    let testCases : List (Nat × Nat × Nat × Rat) := [
      (1, 2, 4, 1),
      (1, 3, 5, 3/4),
      (1, 4, 5, 1/4),
      (2, 4, 6, 1/2),
      (3, 5, 6, 1/4),
      (2, 3, 7, 1/4),
      (2, 3, 8, 1/4),  -- Duplicate (2,3) at different k
      (1, 4, 8, 1/2),  -- Duplicate (1,4) at different k
      (3, 5, 10, 1/2)  -- Duplicate (3,5) at different k
    ]

    for (i, j, k, expectedVal) in testCases do
      let found := data.data.toList.find? (fun e =>
        e.i.val = i && e.j.val = j && e.k = k)
      match found with
      | some e =>
        let match_val := if e.value = expectedVal then "✓" else "✗"
        IO.println s!"  ({i},{j},k={k}) = {e.value} (expected: {expectedVal}) {match_val}"
      | none =>
        IO.println s!"  ({i},{j},k={k}) = NOT FOUND ✗ (expected: {expectedVal})"

    IO.println ""
    IO.println "=== VALIDITY CHECKS ==="

    -- Check for i < j constraint (should always pass due to h_order)
    let invalidPairs := data.data.toList.filter (fun e => e.i.val ≥ e.j.val)
    if invalidPairs.length > 0 then
      IO.println "✗ Found entries where i ≥ j (SHOULD BE IMPOSSIBLE!):"
      for e in invalidPairs do
        IO.println s!"  ({e.i.val},{e.j.val},k={e.k})"
    else
      IO.println "✓ All entries satisfy i < j (enforced by type)"

    -- Check for k > j constraint (should always pass due to h_j_less_k)
    let invalidK := data.data.toList.filter (fun e => e.k ≤ e.j.val)
    if invalidK.length > 0 then
      IO.println "✗ Found entries where k ≤ j (SHOULD BE IMPOSSIBLE!):"
      for e in invalidK do
        IO.println s!"  ({e.i.val},{e.j.val},k={e.k})"
    else
      IO.println "✓ All entries satisfy k > j (enforced by type)"

    -- Check value ranges [0,1]
    let invalidValues := data.data.toList.filter (fun e => e.value < 0 || e.value > 1)
    if invalidValues.length > 0 then
      IO.println "✗ Found entries with values outside [0,1]:"
      for e in invalidValues do
        IO.println s!"  ({e.i.val},{e.j.val},k={e.k}) = {e.value}"
    else
      IO.println "✓ All values in range [0,1]"

    -- Check i ≥ 1 constraint (should always pass due to h_i_bound)
    let invalidI := data.data.toList.filter (fun e => e.i.val < 1)
    if invalidI.length > 0 then
      IO.println "✗ Found entries where i < 1 (SHOULD BE IMPOSSIBLE!):"
      for e in invalidI do
        IO.println s!"  ({e.i.val},{e.j.val},k={e.k})"
    else
      IO.println "✓ All entries satisfy i ≥ 1 (enforced by type)"

    -- Check k ≤ n constraint (should always pass due to h_k_bound)
    let invalidKBound := data.data.toList.filter (fun e => e.k > n)
    if invalidKBound.length > 0 then
      IO.println s!"✗ Found entries where k > n={n} (SHOULD BE IMPOSSIBLE!):"
      for e in invalidKBound do
        IO.println s!"  ({e.i.val},{e.j.val},k={e.k})"
    else
      IO.println s!"✓ All entries satisfy k ≤ n={n} (enforced by type)"

    IO.println ""
    IO.println "=== MIR(10) CONSTRAINT CHECKS ==="
    IO.println ""
    IO.println "Checking Meyniel-Rio (MIR) feasibility constraints..."
    IO.println "1 unit of flow starts from (1,2,3) and flows through the network"
    IO.println ""

    -- Check stage completeness
    IO.println "Stage completeness check:"
    let stagesPresent := [4, 5, 6, 7, 8, 9, 10].filter fun k =>
      data.data.toList.any (fun e => e.k = k)
    IO.println s!"  Stages with data: {stagesPresent}"
    if stagesPresent.length = 7 then
      IO.println "  ✓ All stages from 4 to 10 have data"
    else
      IO.println "  ✗ Missing some stages!"

    IO.println ""
    IO.println "Flow conservation check (total flow = 1 at each layer):"
    for k in [4, 5, 6, 7, 8, 9, 10] do
      let entriesAtK := data.data.toList.filter (fun e => e.k = k)
      let totalFlow : Rat := entriesAtK.foldl (fun acc e => acc + e.value) 0
      let diff := totalFlow - 1
      let status := if diff.abs < 1/100 then "✓" else "✗"
      IO.println s!"  k={k:2}: total flow = {totalFlow}, expected = 1, diff = {diff} {status}"

    IO.println ""
    IO.println "Constraint 2: Flow conservation for each node (i,j)"
    IO.println "(For each node at layer k, inflow from k-1 should equal outflow to k+1)"

    -- For each k from 5 to 9, check flow conservation
    for k in [5, 6, 7, 8, 9] do
      let nodesAtK := data.data.toList.filter (fun e => e.k = k)
      let uniquePairs := nodesAtK.map (fun e => (e.i.val, e.j.val)) |>.eraseDups

      IO.println s!"\n  Layer k={k}:"
      for (i, j) in uniquePairs.take 3 do  -- Show first 3 for brevity
        -- Inflow: entries at k with pair (i,j)
        let inflow := nodesAtK.filter (fun e => e.i.val = i && e.j.val = j)
                              |>.map (·.value) |>.foldl (· + ·) 0

        -- Outflow: entries at k+1 that could come from (i,j)
        -- This is more complex - need to check which (i',j') at k+1 can receive from (i,j) at k
        let nodesAtKp1 := data.data.toList.filter (fun e => e.k = k + 1)
        let outflow := nodesAtKp1.filter (fun e =>
                         -- (i,j) can send to (i',j') if they share an index
                         (e.i.val = i || e.i.val = j || e.j.val = i || e.j.val = j))
                       |>.map (·.value) |>.foldl (· + ·) 0

        let diff := inflow - outflow
        let status := if diff.abs < 1/10 then "✓" else "?"
        IO.println s!"    ({i},{j}): in={inflow}, out={outflow}, diff={diff} {status}"

      if uniquePairs.length > 3 then
        IO.println s!"    ... and {uniquePairs.length - 3} more nodes"

    IO.println ""
    IO.println "Constraint 3: Non-negativity (already enforced by type)"
    IO.println "  ✓ All values ≥ 0 (checked above)"

    IO.println ""
    IO.println "Constraint 4: Unit upper bounds"
    let violations := data.data.toList.filter (fun e => e.value > 1)
    if violations.length > 0 then
      IO.println s!"  ✗ Found {violations.length} entries > 1:"
      for e in violations.take 5 do
        IO.println s!"    ({e.i.val},{e.j.val},k={e.k}) = {e.value}"
    else
      IO.println "  ✓ All values ≤ 1"

    IO.println ""
    IO.println "╔════════════════════════════════════════════════╗"
    IO.println "║              Verification Complete             ║"
    IO.println "╚════════════════════════════════════════════════╝"
    IO.println ""
    IO.println "Note: Full MIR feasibility requires checking detailed"
    IO.println "flow conservation through the entire network structure."
    IO.println "For complete verification, use the FeasibilityCheck module."

/-- Main entry point -/
def main : IO Unit := do
  verifyBookProblemData (n := 10) "Book_problem"
