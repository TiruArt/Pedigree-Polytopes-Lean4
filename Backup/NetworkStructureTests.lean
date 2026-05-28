-- MembershipProject/Core/NetworkStructureTests.lean
-- Tests for NetworkStructure module

import MembershipProject.Core.NetworkStructure

open MembershipProject.Core

-- Test the code
#eval "Testing for n=3:" ++ "\n"
#eval MembershipProject.Core.export_network_structures 3

#eval "\n\nTesting for n=5:" ++ "\n"
#eval MembershipProject.Core.export_network_structures 5

#eval "\n\nTesting for n=8:" ++ "\n"
#eval MembershipProject.Core.export_network_structures 8

-- Additional test: Show nodes in specific layers
#eval "\n\nNodes in layer 3:"
#eval MembershipProject.Core.nodes_in_layer 3 |>.map toString

#eval "\n\nNodes in layer 4:"
#eval MembershipProject.Core.nodes_in_layer 4 |>.map toString

#eval "\n\nNodes in layer 5:"
#eval MembershipProject.Core.nodes_in_layer 5 |>.map toString

-- Test specific arcs for k=3 - should show ALL arcs
#eval "\n\nTesting ALL arcs for k=3:"
#eval let layer3 := MembershipProject.Core.nodes_in_layer 3
      let layer4 := MembershipProject.Core.nodes_in_layer 4
      let all_arcs := List.flatMap (fun nk =>
        layer4.map (fun nkp1 => (nk, nkp1))) layer3
      s!"Total arcs from layer 3 to 4: {all_arcs.length}"
      ++ "\nFirst 10 arcs:"
      ++ String.intercalate "\n" (all_arcs.take 10 |>.map (λ (a,b) => s!"{a} -> {b}"))

-- Test specific arcs for k=4
#eval "\n\nTesting permitted arcs for k=4:"
#eval let test_arcs := permitted_arcs_for_stage 4
      s!"Total permitted arcs from layer 4 to 5: {test_arcs.length}"
      ++ "\nFirst 5 arcs:"
      ++ String.intercalate "\n" (test_arcs.take 5 |>.map (λ (a,b) => s!"{a} -> {b}"))

-- Test the specific arc (1,2,4) -> (3,4,5) for k=4
#eval "\n\nChecking specific arc (1,2,4) -> (3,4,5) for k=4:"
#eval let node_124 : Node := { i := 1, j := 2, k := 4 }
      let node_345 : Node := { i := 3, j := 4, k := 5 }
      s!"Permitted? {is_permitted_arc 4 node_124 node_345}"

-- Test another arc: (1,2,4) -> (1,4,5) for k=4
#eval "\n\nChecking specific arc (1,2,4) -> (1,4,5) for k=4:"
#eval let node_124 : Node := { i := 1, j := 2, k := 4 }
      let node_145 : Node := { i := 1, j := 4, k := 5 }
      s!"Permitted? {is_permitted_arc 4 node_124 node_145}"

-- Test arc: (1,2,4) -> (1,3,5) for k=4
#eval "\n\nChecking specific arc (1,2,4) -> (1,3,5) for k=4:"
#eval let node_124 : Node := { i := 1, j := 2, k := 4 }
      let node_135 : Node := { i := 1, j := 3, k := 5 }
      s!"Permitted? {is_permitted_arc 4 node_124 node_135}"
