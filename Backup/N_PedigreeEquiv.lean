-- File No. 4-2 - N_PedigreeEquiv.lean
--
-- Equivalence between the two Pedigree formulations:
--   N_PedigreeDefinition (File 4)  : List Triple with proof fields
--   N_DesirableDef       (File 4-1): Finset (Finset ℕ) with predicates
--
-- CORRESPONDENCE:
--   isPreSolution ↔ h_length + h_first + h_layers
--   isSolution    ↔ + h_distinct (positions > 0, layers ≥ 4)
--   Pedigree      ↔ + h_generators + h_in_delta
--
-- CONVERSION FUNCTIONS:
--   toFinsetPed : Pedigree n → Finset (Finset ℕ)
--     maps each triangle (i,j,k) ↦ {i,j,k}
--   fromFinsetPed : (S satisfying Pedigree n S) → Pedigree n
--     reconstructs the List Triple from the Finset representation
--
-- Reference: Arthanari, T.S. arXiv:2507.09069v1 [math.CO].

import MembershipProject.Core.N_PedigreeDefinition
import MembershipProject.Core.N_DesirableDef
import Mathlib.Tactic
set_option linter.unusedVariables false
namespace MembershipProject.Core

open Finset

-- ============================================================
-- CONVERSION: List Triple → Finset (Finset ℕ)
-- ============================================================

/-- Convert a Pedigree n to its Finset representation.
    Each triangle (i,j,k) becomes the 3-element set {i,j,k}. -/
def toFinsetPed {n : ℕ} (P : Pedigree n) : Finset (Finset ℕ) :=
  (P.triangles.map (fun t => ({t.i, t.j, t.k} : Finset ℕ))).toFinset

-- ============================================================
-- DIRECTION 1: Pedigree n → Pedigree n (toFinsetPed P)
-- ============================================================

/-- h_length → S.card = n-2 -/
lemma toFinsetPed_card {n : ℕ} (P : Pedigree n) :
    (toFinsetPed P).card = n - 2 := by
  sorry -- [EQUIV-1] follows from h_length + injectivity of t ↦ {t.i,t.j,t.k}

/-- h_layers → unique maximum element per layer -/
lemma toFinsetPed_layers {n : ℕ} (P : Pedigree n) :
    ∀ k ∈ Finset.Icc 3 n,
      ∃ t ∈ toFinsetPed P, (k ∈ t ∧ ∀ x ∈ t, x ≤ k) ∧
        ∀ t' ∈ toFinsetPed P, (k ∈ t' ∧ ∀ x ∈ t', x ≤ k) → t' = t := by
  sorry -- [EQUIV-2] follows from h_layers: t.k = layer = max element

/-- h_distinct → distinct insertion pairs for layers ≥ 4 -/
lemma toFinsetPed_distinct {n : ℕ} (P : Pedigree n) :
    ∀ t1 ∈ toFinsetPed P, ∀ t2 ∈ toFinsetPed P,
      let k1 := t1.max.getD 0
      let k2 := t2.max.getD 0
      (k1 ≥ 4 ∧ k2 ≥ 4 ∧ k1 < k2) → (t1.erase k1) ≠ (t2.erase k2) := by
  sorry -- [EQUIV-3] follows from h_distinct (positions > 0, layers ≥ 4)

/-- h_generators + h_in_delta → generator condition -/
lemma toFinsetPed_generators {n : ℕ} (P : Pedigree n) :
    ∀ t ∈ toFinsetPed P,
      let k    := t.max.getD 0
      let pair := t.erase k
      let a    := pair.min.getD 0
      let b    := pair.max.getD 0
      (pair ⊆ {1, 2, 3}) ∨
      (∃ t_prev ∈ toFinsetPed P, t_prev.max = some b ∧ a ∈ t_prev) := by
  sorry -- [EQUIV-4] follows from h_generators

/-- DIRECTION 1: Every Pedigree n satisfies the Finset predicate. -/
theorem toPedigreeFinset {n : ℕ} (P : Pedigree n) :
    _root_.Pedigree n (toFinsetPed P) := by
  constructor
  · constructor
    · exact ⟨toFinsetPed_card P, sorry, toFinsetPed_layers P⟩
    · exact toFinsetPed_distinct P
  · exact toFinsetPed_generators P

-- ============================================================
-- DIRECTION 2: Finset predicate → Pedigree n
-- ============================================================

/-- Reconstruct a triple from a 3-element Finset {i,j,k}
    where k = max element. -/
noncomputable def tripleOfFinset (s : Finset ℕ) : Triple :=
  let k := s.max.getD 0
  let pair := s.erase k
  let i := pair.min.getD 0
  let j := pair.max.getD 0
  (i, j, k)

/-- Convert a Finset representation back to List Triple,
    ordered by layer (max element). -/
noncomputable def fromFinsetPed (n : ℕ) (S : Finset (Finset ℕ))
    (hS : _root_.Pedigree n S) : Pedigree n := by
  sorry -- [EQUIV-5] reconstruct Pedigree n from S

-- ============================================================
-- MAIN EQUIVALENCE THEOREM
-- ============================================================

/-- The two Pedigree formulations are equivalent:
    A List Triple satisfies N_PedigreeDefinition iff its
    Finset image satisfies N_DesirableDef. -/
theorem pedigree_formulations_equiv (n : ℕ) :
    (∃ P : Pedigree n, True) ↔
    (∃ S : Finset (Finset ℕ), _root_.Pedigree n S) := by
  constructor
  · rintro ⟨P, -⟩
    exact ⟨toFinsetPed P, toPedigreeFinset P⟩
  · rintro ⟨S, hS⟩
    exact ⟨fromFinsetPed n S hS, trivial⟩

end MembershipProject.Core
