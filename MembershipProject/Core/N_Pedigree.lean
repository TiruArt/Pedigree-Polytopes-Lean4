-- Core/N_Pedigree.lean
-- Pedigree structure and basic properties

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_Generators
import MembershipProject.Core.N_Types

namespace MembershipProject.Core

open Nat

-- ============================================================
-- PEDIGREE structure
-- ============================================================

structure Pedigree (n : ℕ) where
  triple_at : ℕ → Triple
  h3       : 3 ≤ n
  h_k_range : ∀ k, 3 ≤ k → k ≤ n → triple_at k ∈ Delta k
  h_base   : triple_at 3 = (1, 2, 3)
  h_distinct : ∀ k1 k2, 4 ≤ k1 → k1 < k2 → k2 ≤ n → triple_at k1 ≠ triple_at k2
  -- Generator property: every triple's generator appears at the correct layer
  h_generator : ∀ k, 4 ≤ k → k ≤ n →
    let t := triple_at k
    let (_, b, _) := t
    if b > 3 then triple_at b ∈ simple_generators t
    else triple_at 3 ∈ simple_generators t

-- ============================================================
-- Convert pedigree to 0-1 LayeredPoint
-- ============================================================

def to_layered {n : ℕ} (P : Pedigree n) : LayeredPoint n :=
  fun t => if P.triple_at t.k = t then 1 else 0

-- ============================================================
-- Midpoint of two pedigrees
-- ============================================================

def midpoint {n : ℕ} (P Q : Pedigree n) : LayeredPoint n :=
  fun t => (to_layered P t + to_layered Q t) / 2

-- ============================================================
-- Pedigree is 0-1 valued
-- ============================================================

lemma pedigree_is_01 {n : ℕ} (P : Pedigree n) (t : Triple) :
    to_layered P t = 0 ∨ to_layered P t = 1 := by
  simp [to_layered]
  by_cases h : P.triple_at t.k = t
  · right; exact h
  · left; exact h

end MembershipProject.Core
