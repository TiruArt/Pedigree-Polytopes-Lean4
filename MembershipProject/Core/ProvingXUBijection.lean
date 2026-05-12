import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open BigOperators

namespace UniqueInsertion

def Triangle (n : ℕ) := Fin n × Fin n × Fin n

instance (n : ℕ) : Fintype (Triangle n) := by unfold Triangle; infer_instance
instance (n : ℕ) : DecidableEq (Triangle n) := by unfold Triangle; infer_instance

def triangles_at_k (n : ℕ) (k : Fin n) : Finset (Triangle n) :=
  Finset.filter (λ t => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 = k) Finset.univ

structure MIR (n : ℕ) where
  x : Triangle n → ℝ
  eq6 : ∀ (k : Fin n) (_ : k.1 ≥ 3), ∑ t ∈ triangles_at_k n k, x t = 1
  nonneg : ∀ t, x t ≥ 0

structure IntegerMIR (n : ℕ) extends MIR n where
  binary : ∀ t, x t = 0 ∨ x t = 1

-- This is the lemma you already have
theorem unique_insertion_sequence (n : ℕ) (k : Fin n) (hk : k.1 ≥ 3) (X : IntegerMIR n) :
    ∃! (t : Triangle n), t ∈ triangles_at_k n k ∧ X.x t = 1 := by
  let S := triangles_at_k n k
  have ex : ∃ t ∈ S, X.x t = 1 := by
    by_contra! h
    have all_zero : ∀ t ∈ S, X.x t = 0 := λ t ht => (X.binary t).resolve_right (h t ht)
    have sum_val : ∑ t ∈ S, X.x t = 1 := X.eq6 k hk
    rw [Finset.sum_congr rfl all_zero] at sum_val
    rw [Finset.sum_const_zero] at sum_val
    linarith
  obtain ⟨t, ht⟩ := ex
  refine ⟨t, ht, λ u ⟨hu, hu_val⟩ => ?_⟩
  by_contra hne
  have h : t ≠ u := Ne.symm hne
  have subset : {t, u} ⊆ S := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    obtain (h1 | h2) := hv
    · rw [h1]; exact ht.1
    · rw [h2]; exact hu
  have le_sum : ∑ v ∈ {t, u}, X.x v ≤ ∑ v ∈ S, X.x v :=
    Finset.sum_le_sum_of_subset_of_nonneg subset (λ v _ _ => X.nonneg v)
  have sum_pair : ∑ v ∈ {t, u}, X.x v = X.x t + X.x u := Finset.sum_pair h
  rw [sum_pair, X.eq6 k hk] at le_sum
  rw [ht.2, hu_val] at le_sum
  linarith

-- ============================================================
-- LayeredPoint: a wrapper around IntegerMIR that gives easy
-- access to the unique insertion edge at each level
-- ============================================================

/-- A layered point is an integer MIR solution with easy access to
    the unique edge for each layer k (3 ≤ k ≤ n). -/
structure LayeredPoint (n : ℕ) where
  mir : IntegerMIR n
  /-- The unique edge (i, j) with i < j < k such that x_{i,j,k} = 1. -/
  edge_at (k : ℕ) (h3 : 3 ≤ k) (hk : k ≤ n) : ℕ × ℕ
  edge_at_spec (k : ℕ) (h3 : 3 ≤ k) (hk : k ≤ n) :
    let (i, j) := edge_at k h3 hk
    i < j ∧ j < k ∧ mir.x ⟨i, j, k, by exact i_lt_j, by exact j_lt_k⟩ = 1

-- ============================================================
-- Helper: get the unique triangle from a LayeredPoint
-- ============================================================

/-- Extract the unique triangle at level k from a layered point. -/
def get_triangle {n : ℕ} (X : LayeredPoint n) (k : ℕ) (h3 : 3 ≤ k) (hk : k ≤ n) :
    Triangle n :=
  let (i, j) := X.edge_at k h3 hk
  ⟨i, j, k, (X.edge_at_spec k h3 hk).1, (X.edge_at_spec k h3 hk).2.1⟩

-- ============================================================
-- Tour construction
-- ============================================================

def tour3 : Finset (ℕ × ℕ) := {(1,2), (1,3), (2,3)}

def insert_edge (T : Finset (ℕ × ℕ)) (i j k : ℕ) : Finset (ℕ × ℕ) :=
  (T.erase (min i j, max i j)) ∪ {(min i k, max i k), (min j k, max j k)}

/-- Build the tour recursively using the unique insertion edges. -/
def build_tour : ∀ (n : ℕ), LayeredPoint n → Finset (ℕ × ℕ)
  | 0, _ => ∅
  | 1, _ => ∅
  | 2, _ => ∅
  | 3, _ => tour3
  | n+1, X => by
      have h3 : 3 ≤ n+1 := by linarith
      let (i, j) := X.edge_at (n+1) h3 (le_refl (n+1))
      let X' : LayeredPoint n :=
        { mir := X.mir,
          edge_at := λ k hk1 hk2 => X.edge_at k hk1 (by linarith [hk2]),
          edge_at_spec := λ k hk1 hk2 => X.edge_at_spec k hk1 (by linarith [hk2]) }
      exact insert_edge (build_tour n X') i j (n+1)

-- ============================================================
-- Slack definition (simplified, using the edge_at information)
-- ============================================================

/-- Recursive slack definition. For n = 3, slack = 1 exactly on the three edges.
    For n+1, we update according to the insertion edge. -/
def U : ∀ (n : ℕ), LayeredPoint n → ℕ → ℕ → ℝ
  | 3, X, i, j =>
      if (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) then 1 else 0
  | n+1, X, i, j => by
      have h3 : 3 ≤ n+1 := by linarith
      let (iₙ, jₙ) := X.edge_at (n+1) h3 (le_refl (n+1))
      let X' : LayeredPoint n :=
        { mir := X.mir,
          edge_at := λ k hk1 hk2 => X.edge_at k hk1 (by linarith [hk2]),
          edge_at_spec := λ k hk1 hk2 => X.edge_at_spec k hk1 (by linarith [hk2]) }
      if i = iₙ ∧ j = jₙ then 0
      else if i = iₙ ∧ j = n+1 then 1
      else if i = jₙ ∧ j = n+1 then 1
      else U n X' i j
  | _, _, _, _ => 0
termination_by U n _ i j => n

-- ============================================================
-- Main theorem: U = 1 iff (i,j) is an edge in build_tour
-- ============================================================

theorem lemma_oneone (n : ℕ) (hn : n ≥ 3) (X : LayeredPoint n) (i j : ℕ) (hij : i < j) :
    U n X i j = 1 ↔ (i, j) ∈ build_tour n X := by
  induction n with
  | zero | one | two => linarith [hn]
  | succ n IH =>
    by_cases n = 2
    · -- Base case: n+1 = 3
      have h3 : n+1 = 3 := by linarith [hn]
      rw [h3] at *
      simp [U, build_tour, tour3, Finset.mem_insert, Finset.mem_singleton]
      fin_cases i <;> fin_cases j <;> decide
    · -- Inductive step: n+1 ≥ 4
      have n_ge_4 : n+1 ≥ 4 := by linarith [hn]
      let k := n+1
      have hk3 : 3 ≤ k := by linarith [hn]
      let (iₙ, jₙ) := X.edge_at k hk3 (le_refl k)
      let X' : LayeredPoint n :=
        { mir := X.mir,
          edge_at := λ k' hk1 hk2 => X.edge_at k' hk1 (by linarith [hk2]),
          edge_at_spec := λ k' hk1 hk2 => X.edge_at_spec k' hk1 (by linarith [hk2]) }
      let T' := build_tour n X'
      have T_eq : build_tour (n+1) X = insert_edge T' iₙ jₙ k := by
        simp [build_tour]
        congr 1
        rfl
      rw [T_eq]
      by_cases h1 : i = iₙ ∧ j = jₙ
      · -- Edge (iₙ, jₙ) is removed
        simp [U, h1, insert_edge, Finset.mem_erase]
        have h_not_in : (iₙ, jₙ) ∉ insert_edge T' iₙ jₙ k := by
          simp [insert_edge, Finset.mem_erase, Finset.mem_union]
          rw [not_or, not_or]
          constructor
          · rw [Finset.mem_erase]; exact λ ⟨_, h⟩ => h rfl
          · rw [Finset.mem_erase]; exact λ ⟨_, h⟩ => h rfl
        simp [h_not_in]
      · by_cases h2 : i = iₙ ∧ j = k
        · -- New edge (iₙ, k) is added
          simp [U, h1, h2, insert_edge, Finset.mem_union]
          have h_in : (iₙ, k) ∈ insert_edge T' iₙ jₙ k := by
            simp [insert_edge, Finset.mem_union]; right; left; rfl
          simp [h_in]
        · by_cases h3 : i = jₙ ∧ j = k
          · -- New edge (jₙ, k) is added
            simp [U, h1, h2, h3, insert_edge, Finset.mem_union]
            have h_in : (jₙ, k) ∈ insert_edge T' iₙ jₙ k := by
              simp [insert_edge, Finset.mem_union]; right; right; rfl
            simp [h_in]
          · -- Unchanged edge: use induction hypothesis
            simp [U, h1, h2, h3]
            have hU_eq : U (n+1) X i j = U n X' i j := rfl
            rw [hU_eq]
            have h_IH : U n X' i j = 1 ↔ (i, j) ∈ T' := IH n (by linarith [hn]) X' i j hij
            rw [h_IH]
            have h_ne1 : (i, j) ≠ (iₙ, jₙ) := by
              intro h_eq; rw [h_eq] at h1; exact h1 h_eq
            have h_ne2 : (i, j) ≠ (iₙ, k) := by
              intro h_eq; rw [h_eq] at h2; exact h2 h_eq
            have h_ne3 : (i, j) ≠ (jₙ, k) := by
              intro h_eq; rw [h_eq] at h3; exact h3 h_eq
            simp [insert_edge, Finset.mem_union, Finset.mem_erase, h_ne1, h_ne2, h_ne3]

end UniqueInsertion
