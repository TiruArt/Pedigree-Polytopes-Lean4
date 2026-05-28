import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Card

set_option linter.unusedSimpArgs false
open SimpleGraph

def hcList (n : ℕ) (i j : Fin n) : List (Fin n) :=
  [i, j] ++ (List.finRange n).filter (fun x => x ≠ i ∧ x ≠ j)

def is_edge_in_cycle {V : Type*} (u v : V) (l : List V) : Prop :=
  ∃ tail : List V, l = u :: v :: tail

theorem hcList_nodup {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (hcList n i j).Nodup := by
  rw [hcList]; apply List.nodup_append.mpr
  refine ⟨by simp [hij], (List.nodup_finRange n).filter _, ?_⟩
  intro x hx y hy hxy
  simp at hx
  simp only [List.mem_filter, List.mem_finRange, true_and,
             decide_eq_true_eq] at hy
  rcases hx with rfl | rfl
  · exact hy.1 hxy.symm
  · exact hy.2 hxy.symm

lemma others_length {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ((List.finRange n).filter (fun x => x ≠ i ∧ x ≠ j)).length = n - 2 := by
  have hnodup : ((List.finRange n).filter (fun x => x ≠ i ∧ x ≠ j)).Nodup :=
    (List.nodup_finRange n).filter _
  have hcard : ((List.finRange n).filter (fun x => x ≠ i ∧ x ≠ j)).toFinset.card =
               ((List.finRange n).filter (fun x => x ≠ i ∧ x ≠ j)).length :=
    List.toFinset_card_of_nodup hnodup
  have heq : ((List.finRange n).filter (fun x => x ≠ i ∧ x ≠ j)).toFinset =
             Finset.univ \ ({i, j} : Finset (Fin n)) := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
               decide_eq_true_eq, Finset.mem_sdiff, Finset.mem_univ,
               Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [← hcard, heq]
  have huniv : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
  have hij2 : ({i, j} : Finset (Fin n)).card = 2 := Finset.card_pair hij
  have hsub : ({i, j} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  have hsdiff : (Finset.univ \ ({i, j} : Finset (Fin n))).card = n - 2 := by
    rw [Finset.card_sdiff]
    simp [huniv, hij2]
  exact hsdiff

theorem complete_graph_has_hc_with_edge
    {n : ℕ} (hn : n ≥ 4) (i j : Fin n) (hij : i ≠ j) :
    ∃ l : List (Fin n),
      l.Nodup ∧ l.length = n ∧ is_edge_in_cycle i j l := by
  refine ⟨hcList n i j, hcList_nodup hij, ?_, ⟨_, rfl⟩⟩
  simp only [hcList, List.length_append, List.length_cons, List.length_nil]
  rw [others_length hij]; omega
