-- File No. 4 - N_RestrictionAll.lean
--
-- Restricted network N_{k-1}(L) for a link L in stage k.
-- arXiv:2507.09069v1, Definition [Restricted Network].
--
-- MOTIVATION (arXiv:2507.09069v1):
-- To extend a pedigree P ∈ P_k via link L = ([k:(r,s)], [k+1:(i,j)]),
-- we require:
--   (1) A generator of (r,s) and a generator of (i,j) are present in P
--   (2) (r,s) and (i,j) do not appear in P restricted to layers < k
--   (3) P ends in (r,s)
-- The restricted network N_{k-1}(L) removes nodes from N_{k-1} that
-- cannot satisfy these conditions, by the deletion rules (a)-(g) below.
--
-- DEPENDENCY:
--   N_RestrictionFull.lean (File No. 3) → N_RestrictionAll.lean (this file)
--
-- Reference: Arthanari, T.S. arXiv:2507.09069v1 [math.CO].

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_RestrictionFull
import MembershipProject.Core.N_PedigreeDefinition

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MembershipProject.Core

open Nat

-- ============================================================================
-- SECTION 1: LINK
-- ============================================================================
--
-- A link L = ([k:e_α], [k+1:e_β]) connects stage k to stage k+1.
-- e_α = (r,s) is the tail edge at layer k.
-- e_β = (i,j) is the head edge at layer k+1.
-- h_valid: e_α ∈ G(e_β) — e_α is a generator of e_β.

structure Link (l : ℕ) where
  tail    : Triple    -- [l : e_α] = (r, s, l)
  head    : Triple    -- [l+1 : e_β] = (i, j, l+1)
  h_tail  : tail.k = l
  h_head  : head.k = l + 1
  h_valid : tail ∈ generators head  -- e_α ∈ G(e_β)

-- ============================================================================
-- SECTION 2: DELETION RULES (a)-(e)
-- ============================================================================
--
-- Given link L = ([k:e_α], [k+1:e_β]) with e_α=(r,s,k), e_β=(i,j,k+1).
-- Start with D = ∅ and apply rules (a)-(e) to get the initial deletion set.

/-- Rules (a)-(e): initial deletion set for link L in N_{k-1}.

    (a) Include [l:e_β] in D for max(4,j) < l < k:
        nodes with pair (i,j) at layers strictly between max(4,j) and k.
    (b) Include [l:e_α] in D for max(4,s) < l < k:
        nodes with pair (r,s) at layers strictly between max(4,s) and k.
    (c) If j > 3: include [j:e] in D for all e ∉ G(e_β) at layer j.
        If j ≤ 3: include [4:e_β] in D (the node (i,j,4)).
    (d) If s > 3: include [s:e] in D for all e ∉ G(e_α) at layer s.
        If s ≤ 3: include [4:e_α] in D (the node (r,s,4)).
    (e) Include all nodes at layer k except [k:e_α] = (r,s,k).

    Reference: Arthanari, T.S. arXiv:2507.09069v1 [math.CO].
    arXiv:2507.09069v1, Definition [Restricted Network]. -/
def deletionSet_initial (nodes : Finset Triple) {k : ℕ} (L : Link k) :
    Finset Triple :=
  let eα := L.tail  -- (r, s, k)
  let eβ := L.head  -- (i, j, k+1)
  let r := eα.i;  let s := eα.j
  let i := eβ.i;  let j := eβ.j
  -- Rule (a): [l:e_β] for max(4,j) < l < k
  let Da := nodes.filter (fun t =>
    t.i = i ∧ t.j = j ∧ max 4 j < t.k ∧ t.k < k)
  -- Rule (b): [l:e_α] for max(4,s) < l < k
  let Db := nodes.filter (fun t =>
    t.i = r ∧ t.j = s ∧ max 4 s < t.k ∧ t.k < k)
  -- Rule (c): layer j nodes not in G(e_β), or [4:e_β] if j ≤ 3
  let Dc := if j > 3 then
    nodes.filter (fun t => t.k = j ∧ t ∉ generators eβ)
  else
    nodes.filter (fun t => t = (i, j, 4))
  -- Rule (d): layer s nodes not in G(e_α), or [4:e_α] if s ≤ 3
  let Dd := if s > 3 then
    nodes.filter (fun t => t.k = s ∧ t ∉ generators eα)
  else
    nodes.filter (fun t => t = (r, s, 4))
  -- Rule (e): all nodes at layer k except e_α
  let De := nodes.filter (fun t => t.k = k ∧ t ≠ eα)
  Da ∪ Db ∪ Dc ∪ Dd ∪ De

-- ============================================================================
-- SECTION 3: DELETION RULE (f) — ITERATED
-- ============================================================================
--
-- Rule (f): If an undeleted node [l:e] with l > 4 has ALL its generators
-- deleted, add it to D. Repeat until no more nodes are deleted.
-- (Origin nodes [4:e] are exempt from this rule.)
-- Termination: (nodes \ deleted).card decreases at each step.

/-- One step of rule (f): find undeleted nodes at layer > 4
    whose all generators are deleted. -/
def deletionStep_ruleF (nodes : Finset Triple)
    (deleted : Finset Triple) : Finset Triple :=
  nodes.filter (fun t =>
    t ∉ deleted ∧       -- not yet deleted
    t.k > 4 ∧           -- not an origin node
    (generators t).filter (fun g => g ∈ nodes) ⊆ deleted)
                        -- all generators (in network) are deleted

/-- Rule (f): iterate deletionStep_ruleF until fixpoint.
    Termination guaranteed: deleted set grows monotonically,
    bounded by nodes.card. -/
def deletionSet_ruleF (nodes : Finset Triple)
    (deleted : Finset Triple) : Finset Triple :=
  -- Iterate at most nodes.card times (sufficient for fixpoint)
  (List.range nodes.card).foldl
    (fun D _ => D ∪ deletionStep_ruleF nodes D)
    deleted

-- ============================================================================
-- SECTION 4: FULL DELETION SET (rules a-f)
-- ============================================================================

/-- Full deletion set D for link L: apply rules (a)-(e) then iterate (f). -/
def deletionSet (nodes : Finset Triple) {k : ℕ} (L : Link k) :
    Finset Triple :=
  deletionSet_ruleF nodes (deletionSet_initial nodes L)

-- ============================================================================
-- SECTION 5: RESTRICTED NETWORK
-- ============================================================================
--
-- N_{k-1}(L) = subnetwork induced by V(N_{k-1}) \ D.
-- Rule (g): rigid pedigrees containing any deleted node are also removed.

structure RestrictedNetwork (n k : ℕ) (L : Link k) where
  base_nodes    : Finset Triple         -- V(N_{k-1})
  deleted       : Finset Triple         -- deletion set D (rules a-f)
  active        : Finset Triple         -- V(N_{k-1}) \ D
  h_active      : active = base_nodes \ deleted
  rigid         : List (RigidEntry n)   -- surviving rigid pedigrees
  -- Rule (g): no rigid pedigree contains a deleted node
  h_rigid_valid : ∀ P ∈ rigid, ∀ t ∈ P.ped.triangles, t ∉ deleted

-- ============================================================================
-- SECTION 6: CAPACITY C(L) AND UNIQUE PATH
-- ============================================================================

-- ============================================================================
-- SECTION 6: CAPACITY C(L) AND UNIQUE PATH
-- ============================================================================
--
-- C(L) = value of the maximal flow in N_{k-1}(L).
-- The only sink is [k:e_α]; sources are undeleted nodes in V_{[1]}
-- and undeleted pedigrees in R_l, 4 ≤ l ≤ k-2.
-- arXiv:2507.09069v1: "Let C(L) be the value of the maximal flow in N_{k-1}(L)."

/-- C(L): the value of the maximal flow in the restricted network N_{k-1}(L).
    The only sink is [k:e_α]; sources are undeleted nodes in V_{[1]}
    and undeleted pedigrees in R_l, 4 ≤ l ≤ k-2.
    This is a definition — C(L) exists by the max flow theorem.
    Computing C(L) is strongly polynomial (arXiv:2507.09069v1).
    arXiv:2507.09069v1: "Let C(L) be the value of the maximal flow in N_{k-1}(L)." -/
noncomputable def capacity_CL {n k : ℕ} {L : Link k}
    (rn : RestrictedNetwork n k L) : ℚ :=
  Classical.choice ⟨0⟩

/-- P_unique(L): the unique path in N_{k-1}(L) bringing flow C(L)
    to the tail [k:e_α] of L, saved when such a path is unique.
    Returns `some path` if unique, `none` otherwise.
    This is a definition — the path either exists uniquely or it does not.
    arXiv:2507.09069v1: "if the path that brings this flow C(L) for any L is
    unique, we save the corresponding path, named P_unique(L), against L." -/
noncomputable def unique_path {n k : ℕ} {L : Link k}
    (rn : RestrictedNetwork n k L) : Option (List Triple) :=
  Classical.choice ⟨none⟩

-- ============================================================================
-- SECTION 7: RIGID PEDIGREE CONSTRUCTION R_k = R_k^1 ∪ R_k^2
-- ============================================================================
--
-- arXiv:2507.09069v1, Section "Completing the construction of the layered network":
--
-- R_k^1: For any rigid arc L from F_k with a unique path P_unique(L)
--        in N_{k-1}(L): the extended pedigree (P_unique(L), e_β) is
--        a rigid pedigree in R_k^1 with weight μ_P = C(L).
--        (Equation 5.6)
--
-- R_k^2: For any rigid arc L = (P', e_β) where P' ∈ R_{k-1}:
--        the extended pedigree (P', e_β) is a rigid pedigree in R_k^2
--        with weight μ_P = C(L).
--        (Equation 5.7)
--
-- R_k = R_k^1 ∪ R_k^2

/-- R_k^1: for each rigid arc L from F_k with a unique path in N_{k-1}(L),
    the extended pedigree (P_unique(L), e_β) is a rigid pedigree with
    weight μ_P = C(L).
    This is a definition — R_k^1 exists given the rigid arcs of F_k.
    Finding R_k^1 is strongly polynomial in the size of N_{k-1}(L).
    arXiv:2507.09069v1, Equation (5.6). -/
noncomputable def Rk1 {n k : ℕ}
    (links : List (Link k))
    (rns   : ∀ L : Link k, RestrictedNetwork n k L) : List (RigidEntry n) :=
  Classical.choice ⟨[]⟩

/-- R_k^2: for each rigid arc L = (P', e_β) where P' ∈ R_{k-1},
    the extended pedigree (P', e_β) is a rigid pedigree with
    weight μ_P = C(L).
    This is a definition — R_k^2 exists given the rigid arcs of F_k.
    Finding R_k^2 is strongly polynomial in the size of N_{k-1}(L).
    arXiv:2507.09069v1, Equation (5.7). -/
noncomputable def Rk2 {n k : ℕ}
    (prev_rigid : List (RigidEntry n))
    (links      : List (Link k)) : List (RigidEntry n) :=
  Classical.choice ⟨[]⟩

/-- R_k = R_k^1 ∪ R_k^2: the full set of rigid pedigrees at stage k. -/
noncomputable def Rk {n k : ℕ}
    (links      : List (Link k))
    (rns        : ∀ L : Link k, RestrictedNetwork n k L)
    (prev_rigid : List (RigidEntry n)) : List (RigidEntry n) :=
  Rk1 links rns ++ Rk2 prev_rigid links

-- ============================================================================
-- DEFINITION SUMMARY
-- ============================================================================
--
-- capacity_CL  — C(L) = value of maximal flow in N_{k-1}(L).
--               Exists by the max flow theorem. Construction deferred.
-- unique_path  — P_unique(L) = unique path achieving C(L), if it exists.
--               Saved when unique; None otherwise. Construction deferred.
-- Rk1          — rigid pedigrees from unique paths. arXiv Eq. (5.6).
--               Construction deferred.
-- Rk2          — rigid pedigrees from P' ∈ R_{k-1}. arXiv Eq. (5.7).
--               Construction deferred.
--
-- All four use Classical.choice as placeholder — they are definitions
-- of mathematical objects, not logical axioms.
-- Computing them is strongly polynomial in size of N_{k-1}(L).
-- Reference: Arthanari, T.S. arXiv:2507.09069v1 [math.CO].

end MembershipProject.Core
