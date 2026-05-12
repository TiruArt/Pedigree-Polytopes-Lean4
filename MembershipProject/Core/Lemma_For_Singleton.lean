import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic

open Nat Finset

-- ============================================
-- Definitions (axiomatized for the proof)
-- ============================================

axiom Pedigree (n : ℕ) : Type

axiom discords {n : ℕ} (P Q : Pedigree n) : Finset ℕ

axiom swap {n : ℕ} (P Q : Pedigree n) (C : Finset ℕ) : Pedigree n

axiom restrict_to {n : ℕ} (X : Pedigree n) (l : ℕ) : Pedigree l

axiom IsPedigree {n : ℕ} (X : Pedigree n) : Prop

axiom welded {n : ℕ} (P Q : Pedigree n) (s l : ℕ) : Prop

-- ============================================
-- Helper axioms (from the paper)
-- ============================================

axiom not_pedigree_implies_welding {n : ℕ} (P Q : Pedigree n) (l : ℕ)
  (h : ¬ IsPedigree (restrict_to (swap P Q {l}) l)) :
  ∃ s, s < l ∧ welded P Q s l

axiom welding_implies_discord {n : ℕ} (P Q : Pedigree n) (s l : ℕ)
  (h : welded P Q s l) : s ∈ discords P Q ∧ l ∈ discords P Q

axiom generator_of_edge {n : ℕ} (P : Pedigree n) (q : ℕ) : ℕ

axiom generator_lt {n : ℕ} (P : Pedigree n) (q : ℕ) : generator_of_edge P q < q

axiom generator_available_in_original {n : ℕ} (P : Pedigree n) (q u : ℕ) : Prop

axiom not_welded_implies_other_generator {n : ℕ} (P Q : Pedigree n) (q l : ℕ)
  (h_not_weld : ¬ welded P Q q l) (h_u_eq_l : generator_of_edge P q = l) :
  generator_available_in_original (swap P Q {l}) q l

axiom pedigree_extension_possible {n : ℕ} (X : Pedigree n) (q : ℕ)
  (h_gen : ∃ u, generator_available_in_original X q u) :
  IsPedigree (restrict_to X q)

axiom smallest_q_violating {n : ℕ} (X : Pedigree n) (l : ℕ)
  (h : ¬ IsPedigree X) :
  ∃ q, l < q ∧ (∀ r, l < r ∧ r < q → IsPedigree (restrict_to X r)) ∧
    ¬ IsPedigree (restrict_to X q)

axiom swap_preserves_generator {n : ℕ} (P Q : Pedigree n) (q u l : ℕ)
  (h_u_neq_l : u ≠ l) (h_gen : generator_available_in_original P q u) :
  generator_available_in_original (swap P Q {l}) q u

axiom restrict_to_full {n : ℕ} (X : Pedigree n) : restrict_to X n = X

-- The generator at level q is always available in the original pedigree
axiom generator_is_available {n : ℕ} (P : Pedigree n) (q : ℕ) :
  generator_available_in_original P q (generator_of_edge P q)

-- ============================================
-- Lemma (For Singleton Component)
-- ============================================

lemma singleton_swap_valid
    {n : ℕ} (hn : 3 ≤ n)
    (P Q : Pedigree n)
    (l : ℕ)
    (hl : l ∈ discords P Q)
    (h_comp : ∀ s ∈ discords P Q, s ≠ l → ¬ welded P Q s l ∧ ¬ welded P Q l s) :
    IsPedigree (swap P Q {l}) ∧ IsPedigree (swap Q P {l}) := by
  constructor
  · -- Prove for swap P Q {l}
    have h_restrict_l : IsPedigree (restrict_to (swap P Q {l}) l) := by
      by_contra h_not_ped
      obtain ⟨s, hs_lt, h_weld⟩ := not_pedigree_implies_welding P Q l h_not_ped
      have hs_neq : s ≠ l := by linarith
      have hs_disc : s ∈ discords P Q := (welding_implies_discord P Q s l h_weld).1
      specialize h_comp s hs_disc hs_neq
      exact h_comp.1 h_weld
    by_cases h_eq : n = l
    · subst h_eq
      rw [← restrict_to_full (swap P Q {n})]
      exact h_restrict_l
    · by_contra h_not_full
      obtain ⟨q, hq_gt_l, hq_min, h_bad⟩ :=
        smallest_q_violating (swap P Q {l}) l h_not_full
      have h_not_weld_q_l : ¬ welded P Q q l := by
        intro h_weld
        have h_q_disc : q ∈ discords P Q := (welding_implies_discord P Q q l h_weld).1
        have h_neq : q ≠ l := by linarith
        specialize h_comp q h_q_disc h_neq
        exact h_comp.1 h_weld
      let u := generator_of_edge P q
      have hu_lt_q : u < q := generator_lt P q
      match eq_or_ne u l with
      | Or.inl h_u_eq_l =>
          have h_gen_avail :=
            not_welded_implies_other_generator P Q q l h_not_weld_q_l h_u_eq_l
          have h_gen : ∃ u, generator_available_in_original (swap P Q {l}) q u :=
            ⟨l, h_gen_avail⟩
          have h_extend := pedigree_extension_possible (swap P Q {l}) q h_gen
          exact h_bad h_extend
      | Or.inr h_u_neq_l =>
          have h_gen_orig := generator_is_available P q
          have h_gen_avail :=
            swap_preserves_generator P Q q u l h_u_neq_l h_gen_orig
          have h_gen : ∃ u, generator_available_in_original (swap P Q {l}) q u :=
            ⟨u, h_gen_avail⟩
          have h_extend := pedigree_extension_possible (swap P Q {l}) q h_gen
          exact h_bad h_extend
  · -- Symmetric case for swap Q P {l}
    sorry
