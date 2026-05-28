-- File No. 1 - N_Basic.lean
-- Foundation: Triple = ℕ × ℕ × ℕ with 1 ≤ i < j < k.
-- Delta l = all valid triples at layer l.
-- Reference: Arthanari, T.S. Pedigree Polytopes, Springer Nature, 2023.

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace MembershipProject.Core

open Nat

-- ============================================================
-- TRIPLE: a node (i, j, k) with 1 ≤ i < j < k
-- Represents: vertex k was inserted into edge (i,j) at layer k.
-- Chapter 3: Multistage Insertion.
-- ============================================================

abbrev Triple := ℕ × ℕ × ℕ

namespace Triple
abbrev i (t : Triple) : ℕ := t.1
abbrev j (t : Triple) : ℕ := t.2.1
abbrev k (t : Triple) : ℕ := t.2.2
end Triple

-- ============================================================
-- DELTA l = { (i, j, l) | 1 ≤ i < j < l }
-- The set of all valid triples at layer l.
-- Triple = ℕ × (ℕ × ℕ) is right-associative, matching Lean 4's
-- product type convention.
-- ============================================================

def Delta (l : ℕ) : Finset Triple :=
  (Finset.Ico 1 l ×ˢ (Finset.Ico 1 l ×ˢ ({l} : Finset ℕ))).filter
    fun t => t.1 < t.2.1

-- ============================================================
-- MEMBERSHIP LEMMAS FOR DELTA
-- ============================================================

@[simp] lemma mem_Delta_iff {l : ℕ} {t : Triple} :
    t ∈ Delta l ↔ 1 ≤ t.i ∧ t.i < t.j ∧ t.j < l ∧ t.k = l := by
  simp only [Delta, Finset.mem_filter, Finset.mem_product,
             Finset.mem_Ico, Finset.mem_singleton, Triple.i, Triple.j, Triple.k]
  constructor
  · rintro ⟨⟨⟨hi1, hil⟩, ⟨hj1, hjl⟩, hk⟩, hij⟩
    exact ⟨hi1, hij, hjl, hk⟩
  · rintro ⟨hi1, hij, hjl, rfl⟩
    exact ⟨⟨⟨hi1, Nat.lt_trans hij hjl⟩, ⟨Nat.lt_trans (by omega) hij, hjl⟩, rfl⟩, hij⟩

lemma mem_Delta_i1  {l : ℕ} {t : Triple} (h : t ∈ Delta l) : 1 ≤ t.i  := (mem_Delta_iff.mp h).1
lemma mem_Delta_ij  {l : ℕ} {t : Triple} (h : t ∈ Delta l) : t.i < t.j := (mem_Delta_iff.mp h).2.1
lemma mem_Delta_jl  {l : ℕ} {t : Triple} (h : t ∈ Delta l) : t.j < l   := (mem_Delta_iff.mp h).2.2.1
lemma mem_Delta_k   {l : ℕ} {t : Triple} (h : t ∈ Delta l) : t.k = l   := (mem_Delta_iff.mp h).2.2.2
lemma mem_Delta_il  {l : ℕ} {t : Triple} (h : t ∈ Delta l) : t.i < l   :=
  Nat.lt_trans (mem_Delta_ij h) (mem_Delta_jl h)
lemma mem_Delta_jlt {l : ℕ} {t : Triple} (h : t ∈ Delta l) : t.j + 1 ≤ l :=
  Nat.succ_le_of_lt (mem_Delta_jl h)
lemma mem_Delta_l3  {l : ℕ} {t : Triple} (h : t ∈ Delta l) : 3 ≤ l := by
  have := mem_Delta_i1 h; have := mem_Delta_ij h; have := mem_Delta_jl h; omega

lemma mem_Delta_self {l : ℕ} (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hjl : j < l) :
    (i, j, l) ∈ Delta l :=
  mem_Delta_iff.mpr ⟨hi, hij, hjl, rfl⟩

lemma Delta_ext {l : ℕ} {s t : Triple}
    (hs : s ∈ Delta l) (ht : t ∈ Delta l)
    (hi : s.i = t.i) (hj : s.j = t.j) : s = t := by
  have hsk := mem_Delta_k hs; have htk := mem_Delta_k ht
  obtain ⟨si, sj, sk⟩ := s; obtain ⟨ti, tj, tk⟩ := t
  simp [Triple.i, Triple.j, Triple.k] at hi hj hsk htk
  simp [hi, hj, hsk, htk]

lemma delta_mem_for_edge {l : ℕ} {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjl : j < l) :
    (Delta l).filter (fun t => t.i = i ∧ t.j = j) = {(i, j, l)} := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_singleton, mem_Delta_iff,
             Triple.i, Triple.j, Triple.k]
  constructor
  · rintro ⟨⟨_, _, _, hk⟩, rfl, rfl⟩
    obtain ⟨ti, tj, tk⟩ := t; simp at hk; simp [hk]
  · intro h; subst h; exact ⟨⟨hi, hij, hjl, rfl⟩, rfl, rfl⟩

-- ============================================================
-- LAYERED POINT AND VECTOR TYPES
-- LayeredPoint n: assigns a rational weight to each triple (i,j,k) with k ≤ n.
-- This represents a point in the MI formulation space.
-- GenVector k, SlackVector k: rational-valued functions on triples at layer k,
-- used in the layered network flow formulation (Chapter 5).
-- ============================================================

def GenVector   (k : ℕ) := Triple → ℚ
def SlackVector (k : ℕ) := Triple → ℚ
def LayeredPoint (n : ℕ) := Triple → ℚ

-- ============================================================
-- SPARSE GENERATION MATRIX
-- Wrapper enforcing k ≥ 3 (layers start at 3).
-- ============================================================

structure SparseGenerationMatrix (k : ℕ) where
  hk : k ≥ 3

end MembershipProject.Core
