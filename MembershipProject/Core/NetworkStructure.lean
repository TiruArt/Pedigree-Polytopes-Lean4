-- Core/NetworkStructure.lean
-- ========================================================
-- Network Structure for Layered Networks
-- Paper: "A Strongly Polynomial Algorithm for Membership
--        in the Pedigree Polytope" by Tiru Arthanari
-- Section 4: Layered Network Construction
-- ========================================================

import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import MembershipProject.Core.Types

namespace MembershipProject.Core


-- Use Node from Types.lean (simple structure with i, j, k)
open MembershipProject.Core

instance : ToString Node where
  toString n := s!"({n.i},{n.j},{n.k})"

/-- Generate all nodes in layer k -/
def nodes_in_layer (k : Nat) : List Node :=
  if k ≥ 3 then
    List.flatMap (λ i_val =>
      let i := i_val + 1
      if i < k then
        List.flatMap (λ j_offset =>
          let j := i + 1 + j_offset
          if j < k then
            if i < j then
              [{ i := i, j := j, k := k }]
            else
              []
          else
            []
        ) (List.range (k - i))
      else
        []
    ) (List.range (k - 1))
  else
    []

/-- Check if arc from (i,j,k) to (i',j',k+1) is permitted -/
def is_permitted_arc (k : Nat) (node_k : Node) (node_kplus1 : Node) : Bool :=
  -- Ensure node_k is in layer k and node_kplus1 is in layer k+1
  if node_k.k ≠ k || node_kplus1.k ≠ k + 1 then
    false
  else
    -- For k=3, all arcs are permitted (no rules applied)
    if k == 3 then
      true
    else
      -- Condition 1: (i,j) ≠ (i',j')
      if node_k.i == node_kplus1.i && node_k.j == node_kplus1.j then
        false
      else
        -- Condition 2: If j' > 3, then i' must be in {i, j}
        let j' := node_kplus1.j
        let i' := node_kplus1.i
        if j' > 3 then
          -- Check if i' is one of the endpoints of the source edge
          i' == node_k.i || i' == node_k.j
        else
          true

/-- Generate all permitted arcs for stage k -/
def permitted_arcs_for_stage (k : Nat) : List (Node × Node) :=
  let layer_k := nodes_in_layer k
  let layer_kplus1 := nodes_in_layer (k+1)

  List.flatMap (fun nk =>
    layer_kplus1.filterMap (fun nkp1 =>
      if is_permitted_arc k nk nkp1 then
        some (nk, nkp1)
      else
        none)) layer_k

/-- Export network structure for stages 4 to n-1 -/
def export_network_structures (n : Nat) : String :=
  let stages := List.range (n - 3) |>.map (· + 4) |>.takeWhile (· < n)
  let structures := stages.map fun k =>
    let arcs := permitted_arcs_for_stage k
    s!"Stage k={k}: {arcs.length} permitted arcs"
  String.intercalate "\n" structures

end MembershipProject.Core
