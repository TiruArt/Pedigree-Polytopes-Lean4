-- Core/MatrixOps.lean
-- ========================================================
-- Matrix Operations for MI-Relaxation
-- Paper: "A Strongly Polynomial Algorithm for Membership
--        in the Pedigree Polytope" by Tiru Arthanari
-- Section 3: Matrix coefficients for MI-relaxation
-- ========================================================

import MembershipProject.Core.Basic

namespace MembershipProject.Core

open Nat

-- ============================================
-- MATRIX COEFFICIENTS
-- ============================================

/-- Matrix coefficients for the MI-relaxation constraints
    Section 3, Equation (3) -/
def matrixCoeff (k : Nat) (_hk : k ≥ 3) (e : Edge k) (v : GenVar k) : Rat :=
  if _h : e.j + 1 = k then
    if v.i = e.i ∨ v.j = e.i then -1 else 0
  else
    if v.i = e.i ∧ v.j = e.j then 1 else 0

-- ============================================
-- SPARSE MATRIX-VECTOR MULTIPLICATION
-- ============================================

def sparseMatVecMulDirect (k : Nat) (_hk : k ≥ 3) (P : GenVector k) (e : Edge k) : Rat :=
  if _h : e.j + 1 = k then
    -- Sum over all r where e.i < r < k
    let sum1 := (Finset.range k).sum fun r =>
      if h1 : e.i < k then
        if h2 : r < k then
          if h3 : e.i < r then
            -P ⟨e.i, r, h1, h2, h3⟩
          else 0
        else 0
      else 0
    -- Sum over all s where s < e.i < k
    let sum2 := (Finset.range k).sum fun s =>
      if h1 : s < k then
        if h2 : e.i < k then
          if h3 : s < e.i then
            -P ⟨s, e.i, h1, h2, h3⟩
          else 0
        else 0
      else 0
    sum1 + sum2
  else
    -- Identity case: just return P[e.i, e.j]
    if h1 : e.i < k then
      if h2 : e.j < k then
        if h3 : e.i < e.j then
          P ⟨e.i, e.j, h1, h2, h3⟩
        else 0
      else 0
    else 0

def sparseMatVecMul (k : Nat) (A : SparseGenerationMatrix k) (P : GenVector k)
    (e : Edge k) : Rat :=
  sparseMatVecMulDirect k A.hk P e

end MembershipProject.Core
