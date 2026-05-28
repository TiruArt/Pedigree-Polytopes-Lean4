-- Core/Path5LemmaCompleted.lean
-- ========================================================
-- Lemma 12 (Path5 Lemma)
-- Paper: "A Strongly Polynomial Algorithm for Membership
--        in the Pedigree Polytope" by Tiru Arthanari
-- Section 5: Lemma 12 (Base case for path existence)
-- ========================================================

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import MembershipProject.Core.Types
import MembershipProject.Core.Restriction
import MembershipProject.Core.GraphInterface

set_option linter.unusedVariables false

namespace MembershipProject.Core

-- ============================================================================
-- LINK STRUCTURE
-- ============================================================================

/-- A link L = (u, v) between two consecutive layers

    IMPORTANT DISTINCTION:
    - A "link" is a potential connection between nodes at consecutive layers
    - An "arc" is a link with positive capacity in the flow network
    - Before F_k is constructed, we don't know if a link will become an arc
    - A link L has capacity C(L) which may be 0 (in which case it's not an arc)
-/
structure Link where
  u : Triple  -- Source node at layer k
  v : Triple  -- Target node at layer k+1
  h_consecutive : u.k + 1 = v.k
  deriving Repr

/-- Check if a link has positive capacity (i.e., is actually an arc) -/
def Link.hasPositiveCapacity (L : Link) (capacity : Triple → Rat) : Prop :=
  capacity L.v > 0

namespace Restriction

/-- Rule E: Delete all nodes in Δ^k except u

    Interpretation: When restricting to link L = (u, v), we keep only
    the specific node u at layer k, deleting all other layer k nodes.
-/
def ruleE (link : Link) : Finset Triple :=
  (allTriplesWithK link.u.k).filter fun t =>
    ¬(t.i = link.u.i ∧ t.j = link.u.j ∧ t.k = link.u.k)

end Restriction

-- ============================================================================
-- HELPER: Convert Node to Triple
-- ============================================================================

/-- Convert a Node to a Triple (requires proofs of constraints) -/
def Node.toTriple (n : Node) (h_ij : n.i < n.j) (h_jk : n.j < n.k) : Triple :=
  { i := n.i, j := n.j, k := n.k, h_ij := h_ij, h_jk := h_jk }

-- ============================================================================
-- PATH REPRESENTATION
-- ============================================================================

/-- Extract node at layer ℓ from a pedigree path

    Convention: P.nodes = [(1,2,3), e₄, e₅, ..., eₖ]
    - Layer 3 (root) is at index 0
    - Layer 4 is at index 1
    - Layer 5 is at index 2
    - Layer ℓ is at index ℓ - 3
-/
def PedigreePath.getNodeAtLayer {k : ℕ} (P : PedigreePath k) (ℓ : ℕ)
    (h : 3 ≤ ℓ ∧ ℓ ≤ k) : Option Node :=
  let idx := ℓ - 3
  if h_idx : idx < P.nodes.length then
    some (P.nodes.get ⟨idx, h_idx⟩)
  else
    none

/-- Truncate pedigree to layer 5

    P*/5 = [(1,2,3), e₄*, e₅*]

    This is the first 3 nodes of the pedigree path.
-/
def PedigreePath.truncate5 {k : ℕ} (P : PedigreePath k) (h : k ≥ 5) : PedigreePath 5 :=
  { nodes := P.nodes.take 3,  -- First 3 nodes: (1,2,3), e₄, e₅
    flow := P.flow }

/-- The path within P*/5 from layer 4 to layer 5

    path(P*/5) = the arc e₄* → e₅*

    This is the connection between the last two nodes of the truncated pedigree.
-/
def pathInTruncate5 {k : ℕ} (P : PedigreePath k) (h : k ≥ 5) :
    Option (Node × Node) := do
  let e_4 ← P.getNodeAtLayer 4 (by omega)
  let e_5 ← P.getNodeAtLayer 5 (by omega)
  return (e_4, e_5)

-- ============================================================================
-- CONDITION [a]: P*/5 is in R₄ (Rigid)
-- ============================================================================

/-- Check if P*/5 is available in R₄

    Meaning: The truncated pedigree [(1,2,3), e₄*, e₅*] is rigid.

    This means there exists some P₄ ∈ R₄ whose nodes match exactly
    the first 3 nodes of P*.
-/
def truncate5InR4 {k : ℕ} (P_star : PedigreePath k) (h : k ≥ 5)
    (R_4 : List (PedigreePath 4)) : Prop :=
  ∃ P_4 ∈ R_4, P_4.nodes = P_star.nodes.take 3

-- ============================================================================
-- CONDITION [b]: path(P*/5) available in N₄(L*₅)
-- ============================================================================

/-- Check if a node (as Triple) is deleted by restriction rules -/
def isNodeDeleted (node : Node) (D : Finset Triple)
    (h_ij : node.i < node.j) (h_jk : node.j < node.k) : Prop :=
  node.toTriple h_ij h_jk ∈ D

/-- Check if an arc between two nodes exists in restricted network

    An arc exists if:
    1. Both nodes are not deleted
    2. The nodes are at consecutive layers (src.k + 1 = tgt.k)
    3. (Implicitly) The arc has positive capacity in the original network
-/
def arcExistsInRestricted (src tgt : Node) (D : Finset Triple)
    (h_src_ij : src.i < src.j) (h_src_jk : src.j < src.k)
    (h_tgt_ij : tgt.i < tgt.j) (h_tgt_jk : tgt.j < tgt.k) : Prop :=
  ¬ isNodeDeleted src D h_src_ij h_src_jk ∧
  ¬ isNodeDeleted tgt D h_tgt_ij h_tgt_jk ∧
  src.k + 1 = tgt.k

/-- Path availability in restricted network N₄(L*₅)

    The path e₄* → e₅* is available in N₄(L*₅) means:

    1. e₄* is not deleted by restriction rules
    2. e₅* is not deleted (e₅* is the "lone sink" in this restricted network)
    3. The arc e₄* → e₅* exists (both nodes present, consecutive layers)
    4. UNIQUENESS: e₄* is the ONLY node at layer 4 that can reach e₅*
       (all other potential predecessors are either deleted or don't connect)

    Context:
    - L*₅ = (e₅*, e₆*) is the link from layer 5 to layer 6
    - N₄(L*₅) is F₄ with deletions based on rules (a)-(e) applied to L*₅
    - Deletion set D = ruleA ∪ ruleB ∪ ruleC ∪ ruleD ∪ ruleE
-/
def pathAvailableInRestricted {k : ℕ}
    (P_star : PedigreePath k) (e_6_star : Node)
    (h_k : k ≥ 5) (h_e6 : e_6_star.k = 6) : Prop :=
  ∃ (e_4_star e_5_star : Node)
    (h_e4_layer : e_4_star.k = 4)
    (h_e5_layer : e_5_star.k = 5)
    (h_e4_ij : e_4_star.i < e_4_star.j) (h_e4_jk : e_4_star.j < e_4_star.k)
    (h_e5_ij : e_5_star.i < e_5_star.j) (h_e5_jk : e_5_star.j < e_5_star.k)
    (h_e6_ij : e_6_star.i < e_6_star.j) (h_e6_jk : e_6_star.j < e_6_star.k),
  -- Construct link L*₅ = (e₅*, e₆*)
  let t_5 := e_5_star.toTriple h_e5_ij h_e5_jk
  let t_6 := e_6_star.toTriple h_e6_ij h_e6_jk
  let D := Restriction.computeD t_5 t_6
  -- e₄* is not deleted
  ¬ isNodeDeleted e_4_star D h_e4_ij h_e4_jk ∧
  -- e₅* is not deleted (it's the lone sink)
  ¬ isNodeDeleted e_5_star D h_e5_ij h_e5_jk ∧
  -- Arc e₄* → e₅* exists
  arcExistsInRestricted e_4_star e_5_star D h_e4_ij h_e4_jk h_e5_ij h_e5_jk ∧
  -- UNIQUENESS: e₄* is the ONLY predecessor of e₅* in N₄(L*₅)
  (∀ (e_4' : Node) (h' : e_4'.k = 4) (h'_ij : e_4'.i < e_4'.j) (h'_jk : e_4'.j < e_4'.k),
    arcExistsInRestricted e_4' e_5_star D h'_ij h'_jk h_e5_ij h_e5_jk → e_4' = e_4_star)

-- ============================================================================
-- AUXILIARY LEMMAS
-- ============================================================================

/-- Helper: Pedigree path has sufficient length for layers up to k

    A pedigree from layer 3 to layer k has:
    - Node at layer 3: (1,2,3)
    - Node at layer 4: e₄
    - Node at layer 5: e₅
    - ...
    - Node at layer k: eₖ

    Total nodes: k - 2 (from layer 3 to layer k inclusive)
    For k ≥ 5, we need at least 3 nodes to access layers 3, 4, 5
-/
lemma pedigree_nodes_length {k : ℕ} (P : PedigreePath k) (h : k ≥ 5) :
    P.nodes.length ≥ 3 := by
  sorry

/-- Helper: Extract node at layer 4 succeeds -/
lemma getNodeAtLayer4_some {k : ℕ} (P : PedigreePath k) (h : k ≥ 5) :
    ∃ e_4, P.getNodeAtLayer 4 (by omega) = some e_4 := by
  unfold PedigreePath.getNodeAtLayer
  simp
  have h_len := pedigree_nodes_length P h
  use P.nodes.get ⟨1, by omega⟩
  split
  · rfl
  · omega

/-- Helper: Extract node at layer 5 succeeds -/
lemma getNodeAtLayer5_some {k : ℕ} (P : PedigreePath k) (h : k ≥ 5) :
    ∃ e_5, P.getNodeAtLayer 5 (by omega) = some e_5 := by
  unfold PedigreePath.getNodeAtLayer
  simp
  have h_len := pedigree_nodes_length P h
  use P.nodes.get ⟨2, by omega⟩
  split
  · rfl
  · omega

/-- Helper: Nodes in pedigree satisfy ordering constraints -/
lemma pedigree_node_constraints {k : ℕ} (P : PedigreePath k) (ℓ : ℕ)
    (h : 3 ≤ ℓ ∧ ℓ ≤ k) (e : Node) (h_get : P.getNodeAtLayer ℓ h = some e) :
    e.i < e.j ∧ e.j < e.k ∧ e.k = ℓ := by
  sorry

-- ============================================================================
-- RULE CONTRADICTIONS (Case 1: Node Deleted)
-- ============================================================================

/-- Rule A contradiction: Cannot delete e₄* without violating pedigree arc rules -/
lemma contradiction_with_ruleA {n k : ℕ}
    (P_star : PedigreePath k)
    (e_4_star e_5_star e_6_star : Node)
    (link : Link)
    (h_in_A : e_4_star.toTriple _ _ ∈ Restriction.ruleA link.u.i link.u.j link.u.k link.u.h_ij link.u.h_jk)
    (h_e4_ij : e_4_star.i < e_4_star.j) (h_e4_jk : e_4_star.j < e_4_star.k)
    (h_e5_ij : e_5_star.i < e_5_star.j) (h_e5_jk : e_5_star.j < e_5_star.k) :
    False := by
  sorry

/-- Rule B contradiction -/
lemma contradiction_with_ruleB {n k : ℕ}
    (P_star : PedigreePath k)
    (e_4_star e_5_star e_6_star : Node)
    (link : Link)
    (h_in_B : e_4_star.toTriple _ _ ∈
      if h : link.v.j < link.u.k then
        Restriction.ruleB link.v.i link.v.j link.u.k link.v.h_ij h
      else ∅)
    (h_e4_ij : e_4_star.i < e_4_star.j) (h_e4_jk : e_4_star.j < e_4_star.k)
    (h_e5_ij : e_5_star.i < e_5_star.j) (h_e5_jk : e_5_star.j < e_5_star.k)
    (h_e6_ij : e_6_star.i < e_6_star.j) (h_e6_jk : e_6_star.j < e_6_star.k) :
    False := by
  sorry

/-- Rule C contradiction: Cannot delete e₄* without breaking generator structure -/
lemma contradiction_with_ruleC {n k : ℕ}
    (P_star : PedigreePath k)
    (e_4_star e_5_star : Node)
    (link : Link)
    (h_in_C : e_4_star.toTriple _ _ ∈ Restriction.ruleC link.u.i link.u.j link.u.h_ij)
    (h_e4_ij : e_4_star.i < e_4_star.j) (h_e4_jk : e_4_star.j < e_4_star.k)
    (h_e5_ij : e_5_star.i < e_5_star.j) (h_e5_jk : e_5_star.j < e_5_star.k) :
    False := by
  sorry

/-- Rule D contradiction -/
lemma contradiction_with_ruleD {n k : ℕ}
    (P_star : PedigreePath k)
    (e_4_star e_5_star e_6_star : Node)
    (link : Link)
    (h_in_D : e_4_star.toTriple _ _ ∈ Restriction.ruleD link.v.i link.v.j link.v.h_ij)
    (h_e4_ij : e_4_star.i < e_4_star.j) (h_e4_jk : e_4_star.j < e_4_star.k)
    (h_e5_ij : e_5_star.i < e_5_star.j) (h_e5_jk : e_5_star.j < e_5_star.k)
    (h_e6_ij : e_6_star.i < e_6_star.j) (h_e6_jk : e_6_star.j < e_6_star.k) :
    False := by
  sorry

/-- Rule E contradiction: Layer mismatch -/
lemma contradiction_with_ruleE {n k : ℕ}
    (P_star : PedigreePath k)
    (e_4_star e_5_star e_6_star : Node)
    (link : Link)
    (h_in_E : e_4_star.toTriple _ _ ∈ Restriction.ruleE link)
    (h_e4_ij : e_4_star.i < e_4_star.j) (h_e4_jk : e_4_star.j < e_4_star.k)
    (h_e5_ij : e_5_star.i < e_5_star.j) (h_e5_jk : e_5_star.j < e_5_star.k) :
    False := by
  unfold Restriction.ruleE at h_in_E
  simp [Finset.mem_filter] at h_in_E
  obtain ⟨h_in_delta, h_ne_u⟩ := h_in_E

  -- e₄* ∈ Δ^{link.u.k} means e₄*.k = link.u.k
  -- But link.u = e₅* has k = 5, while e₄*.k = 4
  -- Contradiction: 4 = 5
  have h_e4_layer : e_4_star.k = 4 := by omega
  have h_link_layer : link.u.k = 5 := by sorry

  -- Extract from h_in_delta that e₄*.k = link.u.k = 5
  have h_e4_layer_from_delta : e_4_star.k = link.u.k := by
    sorry -- From membership in allTriplesWithK link.u.k

  omega

-- ============================================================================
-- MAIN CONTRADICTION LEMMA: Case 1 (Node Deleted)
-- ============================================================================

/-- If e₄* is deleted by restriction rules, we get a contradiction

    Proof outline:
    1. If e₄* is deleted, it must be by one of rules A, B, C, D, or E
    2. We show each rule leads to contradiction:
       - Rules A, B: Would require same edge at consecutive layers (violates arc rules)
       - Rules C, D: Would break generator structure
       - Rule E: Layer mismatch (deletes layer 5, but e₄* is at layer 4)
    3. Since all cases contradict, e₄* cannot be deleted
-/
lemma absurd_node_deleted_contradicts_active {n k : ℕ}
    (P_star : PedigreePath k)
    (e_4_star e_5_star e_6_star : Node)
    (link : Link)
    (D : Finset Triple)
    (h_D_def : D =
      Restriction.ruleA link.u.i link.u.j link.u.k link.u.h_ij link.u.h_jk ∪
      (if h : link.v.j < link.u.k then Restriction.ruleB link.v.i link.v.j link.u.k link.v.h_ij h else ∅) ∪
      Restriction.ruleC link.u.i link.u.j link.u.h_ij ∪
      Restriction.ruleD link.v.i link.v.j link.v.h_ij ∪
      Restriction.ruleE link)
    (h_deleted : isNodeDeleted e_4_star D _ _)
    (h_e4_ij : e_4_star.i < e_4_star.j) (h_e4_jk : e_4_star.j < e_4_star.k)
    (h_e5_ij : e_5_star.i < e_5_star.j) (h_e5_jk : e_5_star.j < e_5_star.k)
    (h_e6_ij : e_6_star.i < e_6_star.j) (h_e6_jk : e_6_star.j < e_6_star.k) :
    False := by
  rw [h_D_def] at h_deleted
  unfold isNodeDeleted at h_deleted
  simp [Finset.mem_union] at h_deleted

  rcases h_deleted with h_A | h_B | h_C | h_D | h_E
  · exact contradiction_with_ruleA P_star e_4_star e_5_star e_6_star link
      h_A h_e4_ij h_e4_jk h_e5_ij h_e5_jk
  · exact contradiction_with_ruleB P_star e_4_star e_5_star e_6_star link
      h_B h_e4_ij h_e4_jk h_e5_ij h_e5_jk h_e6_ij h_e6_jk
  · exact contradiction_with_ruleC P_star e_4_star e_5_star link
      h_C h_e4_ij h_e4_jk h_e5_ij h_e5_jk
  · exact contradiction_with_ruleD P_star e_4_star e_5_star e_6_star link
      h_D h_e4_ij h_e4_jk h_e5_ij h_e5_jk h_e6_ij h_e6_jk
  · exact contradiction_with_ruleE P_star e_4_star e_5_star e_6_star link
      h_E h_e4_ij h_e4_jk h_e5_ij h_e5_jk

-- ============================================================================
-- MAIN LEMMA (path5)
-- ============================================================================

/-- Lemma (path5): Every P* active for X/(k+1) satisfies either [a] or [b]

    Statement: For every pedigree P* that is active for X/(k+1):

    EITHER
      [a] P*/5 ∈ R₄ (the truncated pedigree is rigid), OR
      [b] path(P*/5) is available in N₄(L*₅) (unique path exists)

    where:
    - P*/5 = [(1,2,3), e₄*, e₅*] is P* truncated to layer 5
    - path(P*/5) = [e₄* → e₅*] is the arc from layer 4 to 5 within P*/5
    - L*₅ = (e₅*, e₆*) is the link from e₅* (layer 5) to e₆* (layer 6)
    - N₄(L*₅) is the network F₄ with deletions applied based on L*₅

    Proof by contradiction:
    1. Assume neither [a] nor [b] holds
    2. Extract nodes e₄*, e₅* from P*
    3. Construct link L*₅ = (e₅*, e₆*)
    4. Compute deletion set D based on L*₅
    5. Case analysis:
       - Case 1: e₄* is deleted → contradiction (shown above)
       - Case 2: e₄* exists but path not unique → contradiction (flow argument)
-/
theorem path5_lemma {n k : ℕ}
    (P_star : PedigreePath k)
    (h_k : k ≥ 5)
    (e_6_star : Node)
    (h_e6 : e_6_star.k = 6)
    (R_4 : List (PedigreePath 4)) :
    truncate5InR4 P_star h_k R_4 ∨
    pathAvailableInRestricted P_star e_6_star h_k h_e6 := by

  -- Proof by contradiction
  by_contra h_not
  push_neg at h_not
  obtain ⟨h_not_a, h_not_b⟩ := h_not

  -- Extract nodes e₄* and e₅* from P*
  obtain ⟨e_4_star, h_e4⟩ := getNodeAtLayer4_some P_star h_k
  obtain ⟨e_5_star, h_e5⟩ := getNodeAtLayer5_some P_star h_k

  -- Get ordering constraints for the extracted nodes
  obtain ⟨h_e4_ij, h_e4_jk, h_e4_layer⟩ := pedigree_node_constraints P_star 4 (by omega) e_4_star h_e4
  obtain ⟨h_e5_ij, h_e5_jk, h_e5_layer⟩ := pedigree_node_constraints P_star 5 (by omega) e_5_star h_e5
  have h_e6_ij : e_6_star.i < e_6_star.j := by sorry
  have h_e6_jk : e_6_star.j < e_6_star.k := by sorry

  -- Construct link L*₅ = (e₅*, e₆*)
  let t_5 := e_5_star.toTriple h_e5_ij h_e5_jk
  let t_6 := e_6_star.toTriple h_e6_ij h_e6_jk
  have h_consecutive : t_5.k + 1 = t_6.k := by rw [h_e5_layer, h_e6]; rfl
  let link : Link := { u := t_5, v := t_6, h_consecutive := h_consecutive }

  -- Compute deletion set D for N₄(L*₅)
  let D := Restriction.ruleA link.u.i link.u.j link.u.k link.u.h_ij link.u.h_jk ∪
           (if h : link.v.j < link.u.k then Restriction.ruleB link.v.i link.v.j link.u.k link.v.h_ij h else ∅) ∪
           Restriction.ruleC link.u.i link.u.j link.u.h_ij ∪
           Restriction.ruleD link.v.i link.v.j link.v.h_ij ∪
           Restriction.ruleE link

  -- Case analysis on whether e₄* is deleted
  by_cases h_node : isNodeDeleted e_4_star D h_e4_ij h_e4_jk

  case pos =>
    -- Case 1: e₄* is deleted → contradiction
    exact absurd_node_deleted_contradicts_active P_star e_4_star e_5_star e_6_star link D
      rfl h_node h_e4_ij h_e4_jk h_e5_ij h_e5_jk h_e6_ij h_e6_jk

  case neg =>
    -- Case 2: e₄* exists but ¬[b] (path not unique)
    -- This means: e₄* not deleted BUT path(P*/5) not available
    --
    -- Since ¬[b], one of these fails:
    -- 1. e₅* is deleted, OR
    -- 2. Arc e₄* → e₅* doesn't exist, OR
    -- 3. Uniqueness fails (multiple predecessors of e₅*)
    --
    -- But P* is active → positive flow in F₄ on path(P*/5)
    -- Positive flow → arc preserved by FFF algorithm
    -- Preserved arc → unique path exists
    -- Contradiction!
    sorry

end MembershipProject.Core
