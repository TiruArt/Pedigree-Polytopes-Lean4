-- Core/N_Pedigree.lean
-- Pedigree structure and basic properties

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_Generators
import MembershipProject.Core.N_Types
import MembershipProject.Core.N_PedigreeDefinition
namespace MembershipProject.Core

open Nat




-- ============================================================
-- Convert pedigree to 0-1 LayeredPoint
-- ============================================================

def to_layered {n : ℕ} (P : Pedigree n) : LayeredPoint n :=
  fun t => if P.getAtLayer t.k = P.triangles.get ⟨t.k - 3, P.h_layers t.k⟩ then 1 else 0

-- ============================================================
-- Midpoint of two pedigrees
-- ============================================================

def midpoint {n : ℕ} (P Q : Pedigree_ n) : LayeredPoint n :=
  fun t => (to_layered P t + to_layered Q t) / 2

-- ============================================================
-- Pedigree is 0-1 valued
-- ============================================================

lemma pedigree_is_01 {n : ℕ} (P : Pedigree_ n) (t : Triple) :
    to_layered P t = 0 ∨ to_layered P t = 1 := by
  simp [to_layered]
  by_cases h : P.triple_at t.k = t
  · right; exact h
  · left; exact h

end MembershipProject.Core
