-- Core/N_RestrictionAll.lean
--
-- Full restricted network construction — needed for COMPUTATION and COMPLEXITY
-- (Chapter 6), NOT for the N&S theorem proof (Chapter 5).
--
-- The N&S theorem assumes (N_k, R_k, μ) is well-defined as a precondition
-- encoded in LayeredNetwork n k. This file formalizes HOW to construct it.
--
-- Contents:
--   - Link definition
--   - Deletion rules (a)–(g)  (Chapter 5, Definition restrict, line 141)
--   - Restricted network N_{k-1}(L)
--   - Capacity C(L) = max flow in N_{k-1}(L)
--   - Unique path P_unique(L)
--   - FFF algorithm (Frozen Flow Finding)
--   - Construction of R_k = R_k^1 ∪ R_k^2
--
-- ============================================================================
-- PLACE IN DEPENDENCY ORDER
-- ============================================================================
--
-- N_RestrictionFull.lean     (generators, RigidEntry — theory)
--   ↓
-- N_RestrictionAll.lean      (this file — computation/complexity, Chapter 6)
--
-- NOT imported by N_LayeredNetworkTypes.lean (theory files do not need it)

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_RestrictionFull

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MembershipProject.Core

open Nat

-- ============================================================================
-- SECTION 1: LINK
-- ============================================================================
--
-- Chapter 5, Definition [Link] (line 121):
-- ([l:e], [l+1:e']) is a link if:
--   1. x_l(e) > 0 and x_{l+1}(e') > 0
--   2. either e' ∈ E_l \ E_{l-1} and e ∈ G(e'), or e, e' ∈ E_{l-1} and e ≠ e'

structure Link (l : ℕ) where
  tail    : Triple    -- [l : e_α]
  head    : Triple    -- [l+1 : e_β]
  h_tail  : tail.k = l
  h_head  : head.k = l + 1
  h_valid : tail ∈ generators head  -- e_α ∈ G(e_β)

-- ============================================================================
-- SECTION 2: DELETION SET
-- ============================================================================
--
-- Chapter 5, Definition restrict (line 141):
-- Given link L = ([k:e_α], [k+1:e_β]) with e_α = (r,s), e_β = (i,j),
-- the deletion set D is built by rules (a)–(g).
-- Full implementation deferred to complexity analysis (Chapter 6).

/-- Deletion rules (a)–(e): initial deleted nodes for link L in N_{k-1}.
    Chapter 5, Definition restrict, line 141.
    [DS] Deferred — needed for Chapter 6 complexity analysis. -/
noncomputable def deletionSet_initial {k : ℕ} (nodes : Finset Triple)
    (L : Link k) : Finset Triple :=
  sorry -- [DS] deletion rules (a)-(e)

/-- Rule (f): delete nodes with all generators deleted (iterated).
    Chapter 5, Definition restrict, rule (f).
    [DSF] Deferred — termination by (nodes \ deleted).card. -/
noncomputable def deletionSet_ruleF (nodes : Finset Triple)
    (deleted : Finset Triple) : Finset Triple :=
  sorry -- [DSF] deletion rule (f) — iterated until fixpoint

/-- Full deletion set D for link L (rules a–g).
    [DS] Deferred. -/
noncomputable def deletionSet {k : ℕ} (nodes : Finset Triple)
    (L : Link k) : Finset Triple :=
  sorry -- [DS] full deletion set

-- ============================================================================
-- SECTION 3: RESTRICTED NETWORK
-- ============================================================================
--
-- Chapter 5, Definition restrict (line 141):
-- N_{k-1}(L) = subnetwork induced by V(N_{k-1}) \ D.

structure RestrictedNetwork (n k : ℕ) (L : Link k) where
  base_nodes    : Finset Triple    -- V(N_{k-1})
  deleted       : Finset Triple    -- deletion set D
  active        : Finset Triple    -- V(N_{k-1}) \ D
  h_active      : active = base_nodes \ deleted
  rigid         : List (RigidEntry n)
  h_rigid_valid : ∀ P ∈ rigid, ∀ t ∈ P.triangles, t ∉ deleted

-- ============================================================================
-- SECTION 4: CAPACITY C(L)
-- ============================================================================

/-- C(L) = max flow in N_{k-1}(L).
    [CL] Computed by max flow algorithm — polynomial in network size. -/
noncomputable def capacity_CL {n k : ℕ} {L : Link k}
    (_rn : RestrictedNetwork n k L) : ℚ :=
  sorry -- [CL] max flow in restricted network

/-- Unique path P_unique(L) when C(L) > 0 and path is unique.
    [UP] From max flow decomposition. -/
noncomputable def unique_path {n k : ℕ} {L : Link k}
    (_rn : RestrictedNetwork n k L) : Option (List Triple) :=
  sorry -- [UP] unique path detection

-- ============================================================================
-- SECTION 5: RIGID PEDIGREE CONSTRUCTION
-- ============================================================================
--
-- Chapter 5, §5.2 (lines 263–293):
-- R_k = R_k^1 ∪ R_k^2

/-- R_k^1: rigid pedigrees from unique paths (Chapter 5, eq. 5.6). -/
noncomputable def Rk1 {n k : ℕ}
    (_links : List (Link k))
    (_rns   : ∀ L : Link k, RestrictedNetwork n k L) : List (RigidEntry n) :=
  sorry -- [RK1]

/-- R_k^2: rigid pedigrees from extensions of P' ∈ R_{k-1} (Chapter 5, eq. 5.7). -/
noncomputable def Rk2 {n k : ℕ}
    (_prev_rigid : List (RigidEntry n))
    (_links      : List (Link k)) : List (RigidEntry n) :=
  sorry -- [RK2]

-- ============================================================================
-- SECTION 6: SORRY INVENTORY
-- ============================================================================
--
-- [CL]  capacity_CL    — max flow in restricted network
--                         Computed by standard max flow (low-order polynomial)
--                         Chapter 6 establishes polynomial complexity
--
-- [UP]  unique_path     — unique path detection
--                         From max flow decomposition
--
-- [RK1] Rk1            — rigid pedigrees from unique paths
--                         Chapter 5, eq. (5.6)
--
-- [RK2] Rk2            — extend rigid pedigrees from R_{k-1}
--                         Chapter 5, eq. (5.7)
--
-- [F]   deletionSet_ruleF termination — well-founded on (nodes \ deleted).card

end MembershipProject.Core
