import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Sort
-- This is the most common path for intervals in Mathlib 4
import Mathlib.Order.Interval.Finset.Nat

-- Try this naming if the previous one failed
instance : LocallyFiniteOrder ℕ := Nat.instLocallyFiniteOrder


/-! # PedListEquivalence.lean -/

def IsTriple (t : List ℕ) : Prop :=
  List.Pairwise (· < ·) t ∧ t.length = 3

def listToFinset (S : List (List ℕ)) : Finset (Finset ℕ) :=
  (S.map List.toFinset).toFinset

/-! ### Definitions -/

def isPreSolution (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  S.card = n - 2 ∧ (∀ t ∈ S, t.card = 3) ∧
  (∀ k ∈ Finset.Icc 3 n, ∃! t ∈ S, t.max = some k)

def isSolution (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  isPreSolution n S ∧
  ∀ t1 ∈ S, ∀ t2 ∈ S,
    let k1 := (t1.max).getD 0
    let k2 := (t2.max).getD 0
    (k1 ≥ 4 ∧ k2 ≥ 4 ∧ k1 < k2) → (t1.erase k1) ≠ (t2.erase k2)

def Pedigree (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  isSolution n S ∧ ∀ t ∈ S,
    let k := (t.max).getD 0
    let pair := t.erase k
    let a := (pair.min).getD 0
    let b := (pair.max).getD 0
    (k ≥ 4 → (b ≤ 3 ∨ ∃ t_prev ∈ S, t_prev.max = some b ∧ a ∈ t_prev))

def isPreSolutionList (n : ℕ) (S : List (List ℕ)) : Prop :=
  S.length = n - 2 ∧ S.Nodup ∧ (∀ t ∈ S, IsTriple t) ∧
  (∀ k ∈ (Finset.Icc 3 n).toList, ∃! t ∈ S, t.getLast? = some k)

def isSolutionList (n : ℕ) (S : List (List ℕ)) : Prop :=
  isPreSolutionList n S ∧
  ∀ t1 ∈ S, ∀ t2 ∈ S,
    let k1 := (t1.getLast?).getD 0
    let k2 := (t2.getLast?).getD 0
    (k1 ≥ 4 ∧ k2 ≥ 4 ∧ k1 < k2) → (t1.erase k1) ≠ (t2.erase k2)

def PedigreeList (n : ℕ) (S : List (List ℕ)) : Prop :=
  isSolutionList n S ∧ ∀ t ∈ S,
    let k := (t.getLast?).getD 0
    let pair := t.erase k
    -- Stable Lean 4 bracket indexing
    let i_k := (pair[0]?).getD 0
    let j_k := (pair[1]?).getD 0
    (k ≥ 4 → (j_k ≤ 3 ∨ ∃ t_prev ∈ S, t_prev.getLast? = some j_k ∧ i_k ∈ t_prev))

/-! ### Lemmas -/

lemma toFinset_max_eq_getLast {l : List ℕ} (h_sorted : l.Pairwise (· < ·)) (h_ne : l ≠ []) :
    l.toFinset.max = some (l.getLast h_ne) := by
  have h_mem : l.getLast h_ne ∈ l.toFinset := by simp [List.mem_toFinset, List.getLast_mem h_ne]
  match h_max : l.toFinset.max with


  | none =>
      have h_empty : l.toFinset = ∅ := Finset.max_eq_none.mp h_max
      have h_nonempty : l.toFinset.Nonempty := ⟨l.getLast h_ne, h_mem⟩
      exact h_nonempty.ne_empty h_empty
  | some m =>
      have h_last_le_m : l.getLast h_ne ≤ m := Finset.le_max h_mem h_max
      have h_m_mem : m ∈ l := by
        have := Finset.mem_of_max h_max
        simpa [List.mem_toFinset] using this
      -- Manual bound: in a strictly increasing list, x ∈ l → x ≤ last
      have h_m_le_last : m ≤ l.getLast h_ne := by
        induction l with

        | nil => contradiction
        | cons head tail ih =>
          rw [List.getLast_cons] at *
          split at *
          · simp at h_m_mem; simp [h_m_mem]
          · simp at h_m_mem
            cases h_m_mem with

            | head h_head =>
                subst h_head
                apply Nat.le_of_lt
                -- head < any element in tail, including the last one
                exact h_sorted.1 _ (List.getLast_mem (by assumption))
            | tail h_tail =>
                apply ih (h_sorted.tail) (by assumption) h_tail
      simp [Nat.le_antisymm h_last_le_m h_m_le_last]



lemma toFinset_erase_of_nodup {α : Type _} [DecidableEq α] (l : List α) (h : l.Nodup) (k : α) :
    (l.erase k).toFinset = l.toFinset.erase k := by
  ext x
  -- Standardize the view to List membership
  simp only [List.mem_toFinset, Finset.mem_erase]
  -- Use the core Lean 4 lemma: x ∈ l.erase k ↔ x ≠ k ∧ x ∈ l
  -- This does not require Mathlib specific aliases
  rw [List.mem_erase_iff]
  -- This handles the logic (x ∈ l ∧ x ≠ k ↔ x ≠ k ∧ x ∈ l)
  tauto


lemma erase_equiv (t : List ℕ) (h : IsTriple t) :
    let k := (t.getLast?).getD 0
    (t.erase k).toFinset = (t.toFinset).erase k := by
  let k := (t.getLast?).getD 0
  exact toFinset_erase_of_nodup t (h.1.nodup) k

/-! ### Recommendations for the Theorem -/

theorem pedigree_equivalence (n : ℕ) (S : List (List ℕ))
    (hN : S.Nodup) (hT : ∀ t ∈ S, IsTriple t) :
    PedigreeList n S ↔ Pedigree n (listToFinset S) := by
  -- To prove this, you will need to use:
  -- 1. Finset.card_image_of_injOn (to show card matches length)
  -- 2. last_eq_max (to show max constraints match)
  -- 3. erase_equiv (to show the recursive pedigree step matches)
  sorry
