import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open Finset

/- --- 1. PREDICATES --- -/

def isPreSolution (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  S.card = n - 2 ∧
  (∀ t ∈ S, t.card = 3) ∧
  (∀ k ∈ Icc 3 n, ∃! t ∈ S, t.max = some k)

def isSolution (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  isPreSolution n S ∧
  ∀ t1 ∈ S, ∀ t2 ∈ S,
    let k1 := t1.max.getD 0
    let k2 := t2.max.getD 0
    (k1 ≥ 4 ∧ k2 ≥ 4 ∧ k1 < k2) → (t1.erase k1) ≠ (t2.erase k2)

def isDesiredSolution (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  isSolution n S ∧ ∀ t ∈ S,
    let k := t.max.getD 0
    let pair := t.erase k
    let a := pair.min.getD 0
    let b := pair.max.getD 0
    (pair ⊆ {1, 2, 3}) ∨ (∃ t_prev ∈ S, t_prev.max = some b ∧ a ∈ t_prev)

/- --- 2. THE CONSTRUCTION --- -/

/-- We use a simpler definition that avoids (n-2) inside the function. -/
def Sn (n : ℕ) : Finset (Finset ℕ) :=
  image (fun j => {j + 1, j + 2, j + 3}) (range (n - 2))

/- --- 3. THE PROOF --- -/

theorem Sn_is_desired (n : ℕ) (hn : 3 ≤ n) : isDesiredSolution n (Sn n) := by
  -- Characterize membership clearly to prevent Sn from staying opaque
  have h_mem : ∀ {t}, t ∈ Sn n ↔ ∃ j < n - 2, t = {j + 1, j + 2, j + 3} := by
    intro t; unfold Sn; simp [mem_image, mem_range]

  constructor
  · -- Part 1: isSolution
    constructor
    · -- 1a. isPreSolution
      constructor
      · -- card = n - 2
        unfold Sn; apply card_image_of_injOn
        intro j1 _ j2 _ heq;
        have m1 : ({j1+1, j1+2, j1+3} : Finset ℕ).max = some (j1+3) := by simp; omega
        have m2 : ({j2+1, j2+2, j2+3} : Finset ℕ).max = some (j2+3) := by simp; omega
        rw [heq, m1] at m2; injection m2 with h; omega
      · constructor
        · -- t.card = 3
          intro t ht; rcases h_mem.1 ht with ⟨j, _, rfl⟩
          repeat (apply card_insert_of_not_mem; (intro h; simp at h; omega))
          simp
        · -- Unique max
          intro k hk; simp at hk
          use {k - 2, k - 1, k}
          constructor
          · constructor
            · rw [h_mem]; use k - 3; constructor; omega; repeat (congr; omega)
            · simp; omega
          · intro t ht; rcases ht with ⟨t_in, t_max⟩
            rcases h_mem.1 t_in with ⟨j, _, rfl⟩
            have m_val : ({j+1, j+2, j+3} : Finset ℕ).max = some (j+3) := by simp; omega
            rw [m_val] at t_max; injection t_max with h; subst h; repeat (congr; omega)

    · -- 1b. Non-collision
      intro t1 ht1 t2 ht2
      rcases h_mem.1 ht1 with ⟨j1, _, rfl⟩
      rcases h_mem.1 ht2 with ⟨j2, _, rfl⟩
      have m1 : ({j1+1, j1+2, j1+3} : Finset ℕ).max = some (j1+3) := by simp; omega
      have m2 : ({j2+1, j2+2, j2+3} : Finset ℕ).max = some (j2+3) := by simp; omega
      rw [m1, m2]; simp; intro _ _ h_lt h_erase
      have e1 : ({j1+1, j1+2, j1+3} : Finset ℕ).erase (j1+3) = {j1+1, j1+2} := by apply erase_insert; simp; omega
      have e2 : ({j2+1, j2+2, j2+3} : Finset ℕ).erase (j2+3) = {j2+1, j2+2} := by apply erase_insert; simp; omega
      rw [e1, e2] at h_erase
      have p1 : ({j1+1, j1+2} : Finset ℕ).max = some (j1+2) := by simp; omega
      have p2 : ({j2+1, j2+2} : Finset ℕ).max = some (j2+2) := by simp; omega
      rw [h_erase, p1] at p2; injection p2 with h; omega

  · -- Part 2: isDesiredSolution
    intro t ht
    rcases h_mem.1 ht with ⟨j, _, rfl⟩
    have m_val : ({j+1, j+2, j+3} : Finset ℕ).max = some (j+3) := by simp; omega
    rw [m_val]; simp
    let pair := ({j+1, j+2, j+3} : Finset ℕ).erase (j+3)
    have hp : pair = {j+1, j+2} := by apply erase_insert; simp; omega
    rw [hp]
    have ha : pair.min = some (j+1) := by rw [hp]; simp; omega
    have hb : pair.max = some (j+2) := by rw [hp]; simp; omega
    simp [ha, hb]
    by_cases hj : j = 0
    · left; subst hj; simp; decide
    · right; use { (j-1)+1, (j-1)+2, (j-1)+3 }
      constructor
      · rw [h_mem]; use j - 1; constructor; omega; repeat (congr; omega)
      · constructor <;> (simp; omega)

/- --- 4. VERIFICATION --- -/
#eval (Sn 10).val

#check Sn_is_desired 10
