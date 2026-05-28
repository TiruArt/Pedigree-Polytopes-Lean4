-- Core/N_AdjacencyTheorem_T.lean
-- Main theorem: Adjacency in conv(P_n) iff G_R is connected.

import MembershipProject.Core.N_RigidityGraph_T
import MembershipProject.Core.N_Discords

namespace MembershipProject.Core

theorem adjacency_iff_gr_connected {n : ℕ} (P Q : Pedigree n) :
    AdjacentInPolytope P Q ↔ (rigidityGraph P Q).Connected :=
  sorry

end MembershipProject.Core
