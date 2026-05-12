-- Core/N_Theorem_4_18.lean
-- Theorem 4.18: Adjacent iff G_R connected

import MembershipProject.Core.N_Lemma_4_13
import MembershipProject.Core.N_Theorem_4_19
import MembershipProject.Core.N_Welding
import MembershipProject.Core.N_Pedigree

namespace MembershipProject.Core

open Nat Finset

theorem adjacency_iff_rigidity_graph_connected {n : ℕ} (P Q : Pedigree n) :
    AdjacentInPolytope P Q ↔ True := by
  sorry

end MembershipProject.Core
