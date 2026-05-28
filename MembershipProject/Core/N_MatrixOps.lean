-- File No. 5 - N_MatrixOps.lean
--
-- Sparse matrix-vector multiplication A^{(k)} · P for the MI formulation.
--
-- From the arXiv paper (Definition A_n, A^{(k)}):
--   A^{(k)} = [ I_{p_{k-1}} ]   (old edges: identity rows)
--              [ -M_{k-1}   ]   (new edge: node-edge incidence of K_{k-1})
--
-- For generation vector P : Triple → ℚ and edge t at layer k:
--   New edge (t.j + 1 = k): corresponds to -M_{k-1} row
--     (A^{(k)} · P)(t) = -∑_{r < t.i} P(r, t.i, k)
--                       - ∑_{t.i < s < k} P(t.i, s, k)
--     (negated sum over all triples in G(t) at layer k)
--   Old edge (t.j < k-1): corresponds to I_{p_{k-1}} row
--     (A^{(k)} · P)(t) = P(t.i, t.j, k)
--     (identity: just the generation value at this position)
--
-- Reference: Arthanari, T.S. arXiv:2507.09069v1 [math.CO].

import MembershipProject.Core.N_Basic

namespace MembershipProject.Core

open Nat

-- ============================================================
-- SPARSE MATRIX-VECTOR MULTIPLICATION  (A^{(k)} · P)(t)
-- ============================================================

noncomputable def sparseMatVecMul (k : ℕ) (_hk : SparseGenerationMatrix k)
    (P : GenVector k) (t : Triple) : ℚ :=
  if t.j + 1 = k then
    -- New edge: -M_{k-1} row — negated sum over generators of t
    - (Finset.Ico 1 t.i).sum     (fun r => P (r,   t.i, k)) -
      (Finset.Ico (t.i + 1) k).sum (fun s => P (t.i, s,   k))
  else
    -- Old edge: identity row — generation value at this position
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
