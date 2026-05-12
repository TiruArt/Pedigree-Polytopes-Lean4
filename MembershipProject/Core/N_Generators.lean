-- Core/N_Generators.lean
-- Simple generators definition for adjacency proofs

import MembershipProject.Core.N_Basic

namespace MembershipProject.Core

open Nat

-- ============================================================
-- SIMPLE GENERATORS (for use in adjacency proofs)
-- ============================================================

def simple_generators (t : Triple) : Finset Triple :=
  if t.1 = 1 ∧ t.2.1 = 2 ∧ t.2.2 = 3 then
    ∅
  else if t.2.1 > 3 then
    (Finset.Ico 1 t.1).image (fun r => (r, t.1, t.2.1)) ∪
    (Finset.Ico (t.1 + 1) t.2.1).image (fun s => (t.1, s, t.2.1))
  else
    {(1, 2, 3)}

end MembershipProject.Core
