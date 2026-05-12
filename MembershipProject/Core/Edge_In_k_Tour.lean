import Mathlib.Data.List.FinRange
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.List.Sort
set_option trace.Meta.synthInstance true

open SimpleGraph

/-- In a complete graph, any list with no adjacent duplicates can be a Walk. -/
def hamiltonianWalk {k : ℕ} (i j : Fin k) (l : List (Fin k))
    (h_nodup : l.Nodup) (h_all : l.length = k)
    (h_head : l.head? = some i) (h_last : l.getLast? = some j) :
    (completeGraph (Fin k)).Walk i j := by

  -- 1. Explicitly prove the list is not empty
  have hne : l != [] := by
    intro h; subst h; simp at h_all
    exact Fin.elim0 (h_all ▸ i)

  -- 2. Use 'List.IsChain' specifically from Mathlib
  -- This version does NOT require a Trans instance.
  have h_ischain : List.IsChain (completeGraph (Fin k)).Adj l := by
    -- In Mathlib, isChain_iff_pairwise is the bridge for non-transitive relations
    rw [List.isChain_iff_pairwise]
    exact List.pairwise_of_nodup (λ u v hne_uv => by
      simp [completeGraph]
      exact hne_uv
    ) h_nodup

  -- 3. Construct the walk using the matching 'IsChain' proof
  let w := Walk.ofSupport l hne h_ischain

  -- 4. Cast the endpoints using standardized Mathlib naming
  have hi : l.head hne = i := List.head_of_head?_eq_some h_head
  have hj : l.getLast hne = j := List.getLast_eq_iff_getLast?_eq_some hne |>.mpr h_last

  exact hi ▸ hj ▸ w
/-- Proof that the walk is indeed a Path (no repeated vertices). -/
theorem hamiltonian_is_path {k : ℕ} (l : List (Fin k)) (h_nodup : l.Nodup) (h_all : l.length = k)
    (h_start : l.head? = some i) (h_end : l.getLast? = some j) :
    (hamiltonianWalk l h_nodup h_all h_start h_end).IsPath := by
  rw [Walk.isPath_def]
  -- The 'support' of a walk created from a list is just the list itself
  simp [hamiltonianWalk, Walk.support_toWalk]
  exact h_nodup

/-- Proof that the walk is Spanning (visits every vertex). -/
theorem hamiltonian_is_spanning {k : ℕ} (l : List (Fin k)) (h_nodup : l.Nodup) (h_all : l.length = k)
    (h_start : l.head? = some i) (h_end : l.getLast? = some j) (v : Fin k) :
    v ∈ (hamiltonianWalk l h_nodup h_all h_start h_end).support := by
  simp [hamiltonianWalk, Walk.support_toWalk]
  -- Since length = k and there are no duplicates, the list must contain every element of Fin k
  exact List.mem_iff_get.mpr (List.exists_get_of_nodup_length_eq h_nodup h_all v)




-- Example of constructing a walk in a complete graph on Fin 3
variable (k: Nat)(u v : Fin k)
/-- A walk from 0 to 2 in the complete graph on `Fin k`. -/
def myWalk (k : ℕ) (h : 3 ≤ k) :
    (completeGraph (Fin k)).Walk 0 2 :=
  let g := completeGraph (Fin k)
  -- We construct the walk from right to left using `cons`
  -- 0 -> 1 -> 2
  Walk.cons (by
    -- Proof that 0 and 1 are adjacent in the complete graph
    simp [g]
    -- Since k ≥ 3, 0 and 1 are distinct elements of Fin k
    decide
  ) (Walk.cons (by
    simp [g]
    decide
  ) (Walk.nil))

-- To check the length of the walk
#check (myWalk 3 (by decide)).length -- Output: 2

/-- Theorem: Any edge (i, j) in a complete graph K_k belongs to a Hamiltonian cycle. -/
theorem complete_graph_tour_containing_edge {k : ℕ} (hk : 3 ≤ k)
    (i j : Fin k) (h_edge : i ≠ j) :
    ∃ (p : (completeGraph (Fin k)).Walk i i), p.IsCycle ∧ p.length = k ∧
    (List.zip p.support p.support.tail).Mem (i, j) := by

  -- 1. Construct the vertex list: [i, j, ...others, i]
  let others := (finRange k).filter (λ x => x ≠ i ∧ x ≠ j)
  let v_list := [i, j] ++ others
  let support := v_list ++ [i]

  -- 2. Prove that every consecutive pair in the support is distinct (Adjacency in K_k)
  have h_vlist_nodup : v_list.Nodup := by
    rw [show v_list = i :: j :: others from rfl]
    refine nodup_cons.mpr ⟨?_, nodup_cons.mpr ⟨?_, nodup_filter _ (nodup_finRange k)⟩⟩
    · simp [others]; exact h_edge
    · simp [others]

  have h_adj : ∀ (n : ℕ) (hn : n < support.length - 1),
      (completeGraph (Fin k)).Adj (support.get ⟨n, by omega⟩) (support.get ⟨n + 1, by omega⟩) := by
    intro n hn
    change (support.get ⟨n, by omega⟩) ≠ (support.get ⟨n + 1, by omega⟩)
    apply get_ne_get_of_ne
    · exact h_vlist_nodup
    · omega

  -- 3. Construct the walk from the support
  let p := Walk.ofSupport support h_adj

  -- 4. Provide the witness and prove the properties
  exists p
  refine ⟨⟨Walk.isCircuit_ofSupport _ _, ?_⟩, ?_, ?_⟩
  · -- Prove p.IsCycle via support.tail.Nodup
    simp [p, support, v_list, h_vlist_nodup]
  · -- Prove length = k
    have h_len : others.length = k - 2 := by
      simp [others, length_filter, h_edge, length_finRange]
    simp [p, Walk.length_def, support, v_list, h_len]
    omega
  · -- Prove (i, j) is in the tour
    simp [p, support, v_list]
    left; rfl
