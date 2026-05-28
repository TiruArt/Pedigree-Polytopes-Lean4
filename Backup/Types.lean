-- Core/Types.lean
-- ========================================================
-- Basic Data Structures
-- Paper: "A Strongly Polynomial Algorithm for Membership
--        in the Pedigree Polytope" by Tiru Arthanari
-- Sections 2-3: Preliminaries and MI-Relaxation
-- ========================================================

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace MembershipProject.Core

-- ============================================
-- BASIC GRAPH STRUCTURES
-- ============================================

/-- A node (i,j,k) in the pedigree graph -/
structure Node where
  i : Nat
  j : Nat
  k : Nat
  deriving Repr, DecidableEq, BEq

-- ============================================
-- SPARSE DATA ENTRY
-- ============================================

/-- Single sparse data entry: (i,j,k) → x_ijk with constraints -/
structure SparseEntry (n : ℕ) where
  i : Fin n
  j : Fin n
  k : Nat
  value : Rat
  h_order : i < j
  h_i_bound : 1 ≤ i.val
  h_j_less_k : j.val < k
  h_k_bound : k ≤ n
  h_nonneg : value ≥ 0
  deriving Repr

-- ============================================
-- PARSED DATA STRUCTURE (from files)
-- ============================================

/-- Sparse recursive MIR data structure (for parsing input files) -/
structure ParsedMIRData (n : ℕ) where
  prob_name : String
  data : Array (SparseEntry n)
  pmi_status : Option Bool
  deriving Repr

-- ============================================
-- MIR FEASIBILITY
-- ============================================

/-- A MIR-feasible solution for n cities.
    Section 3: MI-Relaxation -/
structure MIRFeasible (n : ℕ) where
  u : ℕ → ℕ × ℕ → ℚ
  x : ℕ → ℕ × ℕ → ℚ
  h_n : 4 ≤ n
  u_rec : ∀ m, m + 4 ≤ n → ∀ e, u (m + 1) e + x (m + 4) e = u m e
  x_nn : ∀ k e, 0 ≤ x k e
  u_nn : ∀ m e, 0 ≤ u m e
  u0_le1 : ∀ e, u 0 e ≤ 1

-- ============================================
-- CONVEX COMBINATION
-- ============================================

/-- A convex combination of pedigrees at layer k.
    Section 2: Definition of Λ_k(X) -/
structure ConvexCombo (k : ℕ) where
  idx : Finset ℕ
  weight : ℕ → ℚ
  h_nonneg : ∀ r ∈ idx, 0 ≤ weight r
  h_sum : idx.sum weight = 1
  pos : ∀ r ∈ idx, 0 < weight r

end MembershipProject.Core
