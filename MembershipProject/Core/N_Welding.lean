-- Core/N_Welding.lean
-- Welding conditions and graph of rigidity

import MembershipProject.Core.N_Discords
import MembershipProject.Core.N_RestrictionFull

namespace MembershipProject.Core

open Nat

-- ============================================================
-- Edge of a triple
-- ============================================================

def edge_of_triple (t : Triple) : ℕ × ℕ := (t.1, t.2.1)

-- ============================================================
-- Generator availability
-- ============================================================

def generator_available {n : ℕ} (P : Pedigree n) (t : Triple) : Prop :=
  let gen_layer := max 4 t.2.1
  ∃ g ∈ generators t, P.triple_at gen_layer = g

-- ============================================================
-- Welding conditions
-- ============================================================

def condition1_weld {n : ℕ} (P Q : Pedigree n) (q : ℕ) (i : Bool) : Prop :=
  let t := if i then P.triple_at q else Q.triple_at q
  let other := if i then Q else P
  let (_, b, _) := t
  b > 3 ∧ ¬ generator_available other t ∧ b ∈ discords P Q

def condition2_weld {n : ℕ} (P Q : Pedigree n) (q : ℕ) (i : Bool) : Prop :=
  let t := if i then P.triple_at q else Q.triple_at q
  let e := edge_of_triple t
  let other := if i then Q else P
  ∃ s, s < q ∧ s ∈ discords P Q ∧ edge_of_triple (other.triple_at s) = e

-- ============================================================
-- Welded relation: q is welded to s (with s < q)
-- ============================================================

def welded_to {n : ℕ} (P Q : Pedigree n) (q s : ℕ) : Prop :=
  s < q ∧ s ∈ discords P Q ∧ q ∈ discords P Q ∧
  ∃ i : Bool, condition1_weld P Q q i ∨ condition2_weld P Q q i

-- ============================================================
-- Graph of Rigidity: adjacency predicate
-- vertices = discords, edges = unordered pairs where one is welded to the other
-- ============================================================

def are_adjacent {n : ℕ} (P Q : Pedigree n) (s t : ℕ) : Prop :=
  s ∈ discords P Q ∧ t ∈ discords P Q ∧ (welded_to P Q t s ∨ welded_to P Q s t)

-- Symmetry is immediate from definition
lemma adj_symmetric {n : ℕ} (P Q : Pedigree n) (s t : ℕ) :
    are_adjacent P Q s t → are_adjacent P Q t s := by
  intro h
  have hs : s ∈ discords P Q := h.1
  have ht : t ∈ discords P Q := h.2.1
  have h_weld : welded_to P Q t s ∨ welded_to P Q s t := h.2.2
  exact ⟨ht, hs, h_weld.symm⟩

-- Irreflexivity: no self-loops
lemma adj_irreflexive {n : ℕ} (P Q : Pedigree n) (a : ℕ) :
    ¬ are_adjacent P Q a a := by
  intro h
  have h_weld : welded_to P Q a a ∨ welded_to P Q a a := h.2.2
  cases h_weld with
  | inl h' =>
    have h_lt : a < a := h'.1
    exact absurd h_lt (lt_irrefl a)
  | inr h' =>
    have h_lt : a < a := h'.1
    exact absurd h_lt (lt_irrefl a)

end MembershipProject.Core
