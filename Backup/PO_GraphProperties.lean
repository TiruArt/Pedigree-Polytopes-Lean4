import MembershipProject.Core.PO_BasicDefinitions
import MembershipProject.Core.PO_UniqueInsertion
import MembershipProject.Core.PO_SlackIntegrality

namespace PedigreeOpt

open SimpleGraph Finset
open scoped BigOperators
open scoped Classical

/--
  Theorem: The degree of a newly inserted vertex k is exactly 2.
  We prove the neighbor set of k is exactly {i, j} from the unique triangle t.
-/
theorem degree_of_new_vertex_is_two (n : ℕ) (X : IntegerMIR n) (k : Fin n) (hk : k.1 ≥ 3) :
    let G := slack_graph n X.u
    (G.neighborFinset k).card = 2 := by
  -- 1. Use the Unique Insertion theorem to find the unique triangle t = {i, j, k}
  obtain ⟨t, ⟨ht_mem, ht_val⟩, _h_unique⟩ := unique_insertion n k hk X
  let i := t.1
  let j := t.2.1
  let G := slack_graph n X.u

  -- 2. Show that the neighbor set is exactly {i, j}
  have h_neighbors : G.neighborFinset k = {i, j} := by
    ext v
    constructor
    · -- Part A: If v is a neighbor, it must be i or j
      intro h_adj
      simp [slack_graph] at h_adj
      -- This relies on the fact that vertex k only appears in one triangle t
      sorry
    · -- Part B: i and j are indeed neighbors
      intro h_mem
      simp at h_mem
      rcases h_mem with rfl | rfl
      · -- Case v = i: Prove u(i, k) = 1
        simp [slack_graph]
        -- We use the lemma from PO_SlackIntegrality
        have h_i_eq : t.1 = i := rfl
        have h_k_eq : t.2.2 = k := (by simp [DeltaK] at ht_mem; exact ht_mem.2.2)
        exact slack_of_new_edges n X i j k ht_mem h_i_eq h_k_eq
      · -- Case v = j: Prove u(j, k) = 1
        simp [slack_graph]
        -- Similar logic for j
        sorry

  -- 3. Final cardinality proof
  rw [h_neighbors]
  -- To prove card {i, j} = 2, we need i ≠ j
  have h_ne : i ≠ j := by
    simp [DeltaK] at ht_mem
    exact ht_mem.1.ne

  simp [h_ne]

/--
  Theorem: Every vertex in the slack graph has degree 2.
  This is proven by induction: Base case K₃ is 2-regular,
  and each step m -> m+1 maintains regularity via edge-splitting.
-/
theorem slack_graph_regular (n : ℕ) (h_n : n ≥ 3) (X : IntegerMIR n) :
    ∀ (v : Fin n), (slack_graph n X.u).degree v = 2 := by
  intro v
  -- Map degree to neighborFinset card
  rw [SimpleGraph.degree_eq_card_neighborFinset]
  induction n, h_n using Nat.le_induction with

  | base =>
      -- In n=3, the slack graph is exactly K₃
      sorry
  | step m _hm ih =>
      -- In the step, use degree_of_new_vertex_is_two for the new vertex
      -- and show existing vertices maintain degree 2 after edge consumption
      sorry

end PedigreeOpt
