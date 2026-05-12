import MembershipProject.Core.F5Network
import MembershipProject.Algorithms.PythonMaxFlow

namespace MembershipProject.Tests

open F5Network
open MembershipProject.Algorithms

/-- Test 1: Simple 3-node network -/
def testSimpleNetwork : IO Unit := do
  IO.println "Test 1: Simple 3-node network"

  -- Create simple network: source -> mid -> sink
  let source : F5Node := {
    triple := (1, 2, 3)
    capacity := Rat.mk 1 1
  }

  let mid : F5Node := {
    triple := (1, 3, 4)
    capacity := Rat.mk 1 2  -- 1/2
  }

  let sink : F5Node := {
    triple := (2, 4, 5)
    capacity := Rat.mk 1 1
  }

  let edge1 : F5Edge := {
    source := (1, 2, 3)
    target := (1, 3, 4)
    capacity := Rat.mk 3 4  -- 3/4
  }

  let edge2 : F5Edge := {
    source := (1, 3, 4)
    target := (2, 4, 5)
    capacity := Rat.mk 1 1
  }

  let network : F5Network := {
    layer0 := [source]
    layer1 := [mid]
    layer2 := [sink]
    layer3 := []
    layer4 := []
    layer5 := []
    edges := [edge1, edge2]
  }

  -- Compute max-flow
  match ← computeF5MaxFlow network (1, 2, 3) (2, 4, 5) with
  | none => IO.println "  ✗ FAILED: Could not compute max-flow"
  | some flow =>
      let expected := Rat.mk 1 2  -- Bottleneck at mid node with capacity 1/2
      if flow == expected then
        IO.println s!"  ✓ PASSED: Max-flow = {flow} (expected {expected})"
      else
        IO.println s!"  ✗ FAILED: Max-flow = {flow} (expected {expected})"

/-- Test 2: Diamond network with multiple paths -/
def testDiamondNetwork : IO Unit := do
  IO.println "\nTest 2: Diamond network"

  let source : F5Node := {
    triple := (1, 2, 3)
    capacity := Rat.mk 1 1
  }

  let mid1 : F5Node := {
    triple := (1, 3, 4)
    capacity := Rat.mk 1 3  -- 1/3
  }

  let mid2 : F5Node := {
    triple := (2, 3, 4)
    capacity := Rat.mk 2 3  -- 2/3
  }

  let sink : F5Node := {
    triple := (2, 4, 5)
    capacity := Rat.mk 1 1
  }

  let edges : List F5Edge := [
    { source := (1, 2, 3), target := (1, 3, 4), capacity := Rat.mk 1 2 },
    { source := (1, 2, 3), target := (2, 3, 4), capacity := Rat.mk 1 2 },
    { source := (1, 3, 4), target := (2, 4, 5), capacity := Rat.mk 1 1 },
    { source := (2, 3, 4), target := (2, 4, 5), capacity := Rat.mk 1 1 }
  ]

  let network : F5Network := {
    layer0 := [source]
    layer1 := [mid1, mid2]
    layer2 := [sink]
    layer3 := []
    layer4 := []
    layer5 := []
    edges := edges
  }

  -- Compute max-flow
  match ← computeF5MaxFlow network (1, 2, 3) (2, 4, 5) with
  | none => IO.println "  ✗ FAILED: Could not compute max-flow"
  | some flow =>
      let expected := Rat.mk 5 6  -- 1/3 + 1/2 = 5/6
      if flow == expected then
        IO.println s!"  ✓ PASSED: Max-flow = {flow} (expected {expected})"
      else
        IO.println s!"  ✗ FAILED: Max-flow = {flow} (expected {expected})"

/-- Test 3: Check polytope membership -/
def testPolytopeMembership : IO Unit := do
  IO.println "\nTest 3: Polytope membership check"

  -- Create a simple network where source capacity is 1
  let source : F5Node := {
    triple := (1, 2, 3)
    capacity := Rat.mk 1 1
  }

  let sink : F5Node := {
    triple := (1, 3, 4)
    capacity := Rat.mk 1 1
  }

  let edge : F5Edge := {
    source := (1, 2, 3)
    target := (1, 3, 4)
    capacity := Rat.mk 1 1
  }

  let network : F5Network := {
    layer0 := [source]
    layer1 := [sink]
    layer2 := []
    layer3 := []
    layer4 := []
    layer5 := []
    edges := [edge]
  }

  -- Check membership (should be true if max-flow == source capacity)
  let result ← checkPolytopeMembership network (1, 2, 3) (1, 3, 4)

  if result then
    IO.println "  ✓ PASSED: Point is in polytope"
  else
    IO.println "  ✗ FAILED: Point should be in polytope"

/-- Run all tests -/
def runAllTests : IO Unit := do
  IO.println "=========================================="
  IO.println "Python Integration Tests"
  IO.println "==========================================\n"

  testSimpleNetwork
  testDiamondNetwork
  testPolytopeMembership

  IO.println "\n=========================================="
  IO.println "Tests Complete"
  IO.println "=========================================="

end MembershipProject.Tests

/-- Main entry point -/
def main : IO Unit := MembershipProject.Tests.runAllTests
