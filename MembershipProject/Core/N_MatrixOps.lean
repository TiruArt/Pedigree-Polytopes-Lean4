-- Core/N_MatrixOps.lean
-- Matrix operations for MI-Relaxation. Section 3, Equation (3).
-- Triple = ℕ × ℕ × ℕ; edge t at layer k means t.k = k.

import MembershipProject.Core.N_Basic

namespace MembershipProject.Core

open Nat

-- ============================================================
-- SPARSE MATRIX-VECTOR MULTIPLICATION  A^(k) · P
--
-- For generation vector P : Triple → ℚ and edge t at layer k:
--   new edge (t.j = k-1):  (A^k · P)(t) = -∑_{r<t.i} P(r,t.i,k)
--                                         - ∑_{t.i<s<k} P(t.i,s,k)
--   old edge (t.j < k-1):  (A^k · P)(t) = P(t.i, t.j, k)
-- ============================================================

noncomputable def sparseMatVecMul (k : ℕ) (_hk : SparseGenerationMatrix k)
    (P : GenVector k) (t : Triple) : ℚ :=
  if t.j + 1 = k then
    -- new edge
    - (Finset.Ico 1 t.i).sum     (fun r => P (r,   t.i, k)) -
      (Finset.Ico (t.i + 1) k).sum (fun s => P (t.i, s,   k))
  else
    -- old edge: identity lookup
    P (t.i, t.j, k)

-- ============================================================
-- KEY LEMMAS
-- ============================================================

lemma sparseMatVecMul_new (k : ℕ) (hk : SparseGenerationMatrix k)
    (P : GenVector k) (t : Triple) (h : t.j + 1 = k) :
    sparseMatVecMul k hk P t =
    - (Finset.Ico 1 t.i).sum (fun r => P (r, t.i, k)) -
      (Finset.Ico (t.i + 1) k).sum (fun s => P (t.i, s, k)) := by
  simp [sparseMatVecMul, h]

lemma sparseMatVecMul_old (k : ℕ) (hk : SparseGenerationMatrix k)
    (P : GenVector k) (t : Triple) (h : ¬(t.j + 1 = k)) :
    sparseMatVecMul k hk P t = P (t.i, t.j, k) := by
  simp [sparseMatVecMul, h]

end MembershipProject.Core
