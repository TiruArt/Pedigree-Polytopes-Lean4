-- N_HC2Pedigree_hpair.lean
-- Mathematical justification for partialPedigree_hpair_list.
--
-- STATEMENT: No triangle in partialPedigree k i j has pair (i,j).
--
-- PROOF (by contrapositive, Chapter 3):
-- Suppose (i,j) is used as an insertion pair at some layer l.
-- Then vertex l is inserted into edge (i,j):
--   - Edge (i,j) is REMOVED from the current tour
--   - Edges (i,l) and (j,l) are ADDED
-- Therefore (i,j) is no longer in the tour after layer l.
-- In particular, (i,j) is NOT in the final k-tour.
--
-- Contrapositive: if (i,j) IS in the k-tour (as given by
-- partialHC k i j having i and j adjacent), then (i,j) was
-- NEVER used as an insertion pair at any layer.
--
-- Reference: Arthanari, T.S. Pedigree Polytopes,
-- Springer Nature, 2024. Chapter 3 (Multistage Insertion).

import MembershipProject.Core.N_HC2Pedigree
import Mathlib.Tactic

namespace MembershipProject.Core

/-- **Axiom** (pending formal proof):
    No triangle in partialPedigree k i j has insertion pair (i,j).

    **Mathematical proof (contrapositive, Chapter 3)**:
    Suppose (i,j) is used as an insertion pair at layer l.
    Then vertex l is inserted into edge (i,j): edge (i,j) is
    removed and edges (i,l), (j,l) are added. So (i,j) is not
    in the tour after layer l, hence not in the final k-tour.

    Contrapositive: since (i,j) IS in the k-tour of
    partialHC k i j (i and j are adjacent at positions 0 and 1),
    (i,j) was never used as an insertion pair at any layer.

    **Computational evidence**: native_decide confirms k=4..12.

    **TODO**: Formal Lean 4 proof by induction on hcToTriangles,
    using the invariant that (i,j) remains a cycle edge until
    contradicted — which it cannot be since it is in the k-tour.

    **Reference**: Arthanari, T.S. *Pedigree Polytopes*,
    Springer Nature, 2024. Chapter 3. -/
axiom partialPedigree_hpair_list (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    ∀ pos, ∀ hpos : pos < (partialPedigree k i j hk hi hij hjk).triangles.length,
      ((partialPedigree k i j hk hi hij hjk).triangles.get ⟨pos, hpos⟩).i ≠ i ∨
      ((partialPedigree k i j hk hi hij hjk).triangles.get ⟨pos, hpos⟩).j ≠ j

end MembershipProject.Core
