import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option linter.unusedVariables false
open SimpleGraph

/--
In the complete graph K_k (k ≥ 3), for any distinct vertices i and j,
there exists a Hamiltonian cycle where i and j are adjacent.
-/
theorem exists_hamiltonian_cycle_with_adjacent (k : ℕ) (hk : k ≥ 3)
    (i j : Fin k) (hij : i ≠ j) :
    ∃ (G : SimpleGraph (Fin k)), G = ⊤ ∧ ∃ (C : List (Fin k)),
      ∃ (hlen : C.length = k + 1),
      ∃ (h0 : 0 < C.length) (h1 : 1 < C.length) (hk_lt : k < C.length),
      C[0]'h0 = i ∧
      C[1]'h1 = j ∧
      C[k]'hk_lt = i ∧
      List.Nodup (C.take k) ∧
      ∀ (idx : ℕ) (hidx : idx < k),
        ∃ (h_idx : idx < C.length) (h_idx1 : idx + 1 < C.length),
        G.Adj (C[idx]'h_idx) (C[idx + 1]'h_idx1) := by

  -- Define the graph
  let G : SimpleGraph (Fin k) := ⊤

  -- Build our underlying list segments
  let S : Finset (Fin k) := (Finset.univ.erase i).erase j
  let others : List (Fin k) := S.toList
  let L : List (Fin k) := [i, j] ++ others

  -- Prove the length of others using explicit set erasure
  have h_others_len : others.length = k - 2 := by
    dsimp [others, S]
    rw [Finset.length_toList, Finset.card_erase_of_mem]
    · rw [Finset.card_erase_of_mem]
      · simp
        omega
      · simp
    · simp [hij.symm]

  -- Prove total length of L
  have h_L_len : L.length = k := by
    dsimp [L]
    simp [h_others_len]
    omega

  -- Define f using a safe boundary wrapper over L
  let f : Fin (k + 1) → Fin k := fun x ↦
    if h : x.val < k then
      L[x.val]'(by omega)
    else
      i

  let C := List.ofFn f

  use G, rfl
  use C

  -- Length is proven definitionally via List.length_ofFn
  have hlen : C.length = k + 1 := by
    dsimp [C]
    rw [List.length_ofFn]
  use hlen

  -- Supply explicit signature constraints
  have h0 : 0 < C.length := by omega
  have h1 : 1 < C.length := by omega
  have hk_lt : k < C.length := by omega
  use h0, h1, hk_lt

  -- Separate each tuple goal cleanly
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- 1. Prove C = i
    dsimp [C, f]
    rw [List.getElem_ofFn]
    have h_lt : 0 < k := by omega
    simp [h_lt]
    rfl
  · -- 2. Prove C = j
    dsimp [C, f]
    rw [List.getElem_ofFn]
    have h_lt : 1 < k := by omega
    simp [h_lt]
    rfl
  · -- 3. Prove C[k] = i
    dsimp [C, f]
    rw [List.getElem_ofFn]
    simp
  · -- 4. Prove List.Nodup (C.take k)
    have h_take_eq_L : C.take k = L := by
      apply List.ext_getElem
      · dsimp [C]; rw [List.length_take, hlen]; simp; omega
      · intro idx h_left h_right
        rw [List.getElem_take]
        dsimp [C, f]
        rw [List.getElem_ofFn]
        have h_lt : idx < k := by
          dsimp [C] at h_left
          rw [List.length_take, hlen] at h_left
          simp at h_left
          omega
        simp [h_lt]
    rw [h_take_eq_L]

    change (i :: j :: others).Nodup
    apply List.Nodup.cons
    · simp
      refine ⟨hij, ?_⟩
      dsimp [others, S]
      rw [Finset.mem_toList]
      simp
    · apply List.Nodup.cons
      · dsimp [others, S]
        intro h_mem
        have h_fin := Finset.mem_toList.mp h_mem
        simp at h_fin
      · exact Finset.nodup_toList S
  · -- 5. Prove Adjacency G.Adj (C[idx]) (C[idx+1])
    intro idx hidx
    have h_idx : idx < C.length := by omega
    have h_idx1 : idx + 1 < C.length := by omega
    use h_idx, h_idx1
    change SimpleGraph.Adj ⊤ (C[idx]'h_idx) (C[idx + 1]'h_idx1)
    rw [top_adj]

    dsimp [C, f]
    rw [List.getElem_ofFn, List.getElem_ofFn]
    have h_idx_lt : idx < k := by omega
    simp [h_idx_lt]

    by_cases h0 : idx = 0
    · subst h0
      have h1_lt : 1 < k := by omega
      simp [h1_lt]
      exact hij
    · by_cases h1 : idx = 1
      · subst h1
        by_cases h2_lt : 2 < k
        · simp [h2_lt]
          intro h_contra
          dsimp [L] at h_contra
          have h_mem : others[0]'(by omega) ∈ others := List.getElem_mem _
          rw [← h_contra] at h_mem
          dsimp [others, S] at h_mem
          have h_fin := Finset.mem_toList.mp h_mem
          simp at h_fin
        · have hk3 : k = 3 := by omega
          simp [hk3]
          intro h_contra
          dsimp [L] at h_contra
          have h_mem : others[0]'(by omega) ∈ others := List.getElem_mem _
          rw [← h_contra] at h_mem
          dsimp [others, S] at h_mem
          have h_fin := Finset.mem_toList.mp h_mem
          simp at h_fin
      · -- General path case where idx > 1
        by_cases h_end : idx + 1 = k
        · -- Case A: The final element wrapping around back to i
          simp [h_end]
          intro h_contra
          rcases idx with _ | _ | idx_minus_2
          · contradiction
          · contradiction
          · dsimp [L] at h_contra
            have h_mem_others : others[idx_minus_2] ∈ others := List.getElem_mem _
            rw [h_contra] at h_mem_others
            dsimp [others, S] at h_mem_others
            have h_fin := Finset.mem_toList.mp h_mem_others
            simp at h_fin
        · -- Case B: Moving between two consecutive items entirely inside others
          have h_next_lt : idx + 1 < k := by omega
          simp [h_next_lt]
          intro h_contra
          have h_others_nodup : others.Nodup := Finset.nodup_toList S

          dsimp [L] at h_contra
          rcases idx with _ | _ | idx_minus_2
          · contradiction
          · contradiction
          · simp at h_contra
            have h_inj := (List.nodup_iff_injective_getElem).mp h_others_nodup
            have h_eq_idx : (⟨idx_minus_2, by omega⟩ : Fin others.length) = ⟨idx_minus_2 + 1, by omega⟩ := by
              apply h_inj
              exact h_contra
            have h_val_eq := Fin.ext_iff.mp h_eq_idx
            dsimp at h_val_eq
            omega
