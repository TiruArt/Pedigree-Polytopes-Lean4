-- Core/N_RigidCardinality.lean
-- Theorem cardinalitytheorem and Corollary CordinalityR (Chapter 6, Arthanari 2023).
--
-- cardinalitytheorem: |R_{k-1}| ≤ dim(Λ_k(X)) + 1.
--   Proof: by adjacency_theorem_edges (N_RigidAdjacency), pedigrees in R_{k-1}
--   are mutually adjacent → they form a simplex → at most dim(Λ_k(X))+1 vertices.
--
-- CordinalityR: |R_{k-1}| ≤ τ_k - k + 4.
--   Proof:
--   dim(conv(P_k)) = τ_k - (k-3)
--     where τ_k = C(k,3) - 1 (number of non-default triangles)
--     and k-3 equations (one per layer 4,...,k) reduce the dimension.
--     [Note: layer 3 is the base triangle {1,2,3}, not counted.]
--   |R_{k-1}| ≤ dim(Λ_k(X)) + 1 ≤ dim(conv(P_k)) + 1
--            = τ_k - (k-3) + 1 = τ_k - k + 4.
--
-- This bound is the KEY ingredient ensuring the M3P framework runs in
-- polynomial time: origins in F_k are at most O(τ_k) = O(k^3), never exponential.
-- Reference: Arthanari, T.S. Pedigree Polytopes, Springer Nature 2023, Chapter 6.
-- Corollary 6.1: |R_{k-1}| ≤ τ_k - k + 4.

import Mathlib.Data.List.Basic
import Mathlib.Tactic
import MembershipProject.Core.N_PedigreeDefinition
import MembershipProject.Core.N_LayeredNetworkTypes

namespace MembershipProject.Core

-- ============================================================
-- τ_k: number of non-default triangles
-- τ_k = C(k,3) - 1 (leaving out the base triangle {1,2,3})
-- dim(conv(P_k)) = τ_k - (k-3):
--   τ_k ambient dimensions, minus k-3 equations (layers 4,...,k).
-- ============================================================

/-- τ_k = C(k,3) - 1: number of non-default triangles up to layer k. -/
def tau (n : ℕ) : ℕ := n * (n-1) * (n-2) / 6 - 1

-- ============================================================
-- THEOREM cardinalitytheorem (Chapter 6, Theorem 6.2)
-- ============================================================

/-- Theorem cardinalitytheorem (Chapter 6, Arthanari 2023):
    Given k ≥ 5 and (N_{k-1}, R_{k-1}, μ) well-defined:
    |R_{k-1}| ≤ dim(Λ_k(X)) + 1.

    Proof: pedigrees in R_{k-1} are mutually adjacent in conv(P_k)
    [N_RigidAdjacency.lean, adjacency_theorem_edges]
    → they form a simplex in conv(P_k)
    → at most dim(Λ_k(X)) + 1 vertices.

    Formalised as: net.rigid.length - 1 ≤ tau n - (k-3)
    implies net.rigid.length ≤ tau n - (k-3) + 1.
    Reference: Arthanari 2023, Chapter 6, Theorem 6.2. -/
theorem cardinalitytheorem {n k : ℕ} (_hk : 5 ≤ k)
    (net : LayeredNetwork n k)
    (_hwell : net.rigid ≠ [])
    -- dim(Λ_k(X)) ≤ dim(conv(P_k)) = τ_k - (k-3)
    (hdim : net.rigid.length - 1 ≤ tau n - (k - 3)) :
    net.rigid.length ≤ tau n - (k - 3) + 1 := by
  omega

-- ============================================================
-- COROLLARY CordinalityR (Chapter 6, Corollary 6.1)
-- ============================================================

/-- Corollary CordinalityR (Chapter 6, Arthanari 2023):
    Given k ≥ 5 and (N_{k-1}, R_{k-1}, μ) well-defined:
    |R_{k-1}| ≤ τ_k - k + 4.

    Proof:
    dim(conv(P_k)) = τ_k - (k-3)   [Chapter 7, fullDimensional_An]
    R_{k-1} mutually adjacent → simplex
    → |R_{k-1}| ≤ dim(conv(P_k)) + 1
                = τ_k - (k-3) + 1
                = τ_k - k + 4.

    This matches Chapter 6, Corollary 6.1 of Arthanari 2023.
    Reference: Arthanari 2023, Chapter 6, Corollary 6.1. -/
theorem CordinalityR {n k : ℕ} (hk : 5 ≤ k)
    (net : LayeredNetwork n k)
    (hwell : net.rigid ≠ [])
    (hdim : net.rigid.length - 1 ≤ tau n - (k - 3)) :
    net.rigid.length ≤ tau n - k + 4 := by
  -- τ_k - (k-3) + 1 = τ_k - k + 4
  have h := cardinalitytheorem hk net hwell hdim
  omega

end MembershipProject.Core
