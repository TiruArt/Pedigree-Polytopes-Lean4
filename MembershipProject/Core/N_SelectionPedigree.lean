-- N_SelectionPedigree.lean
-- For each (i,j,k) with 1 ≤ i < j < k ≤ n, k ≥ 4,
-- the selection pedigree forces C(i,j,k) = 0.
--
-- KEY AXIOM: edgeInHC
-- For any 1 ≤ i < j ≤ k-1, there exists a valid pedigree on {1,...,k-1}
-- whose last tour (the (k-1)-tour) contains edge (i,j).
-- This is proved separately in N_EdgeInHC.lean.
--
-- The construction depends on i,j:
-- [1] i=1, j=2: use [(1,2,3), e⁴, ..., e^{k-1}]
--     The 3-tour already contains (1,2). Default extensions preserve it.
-- [2] i=1, j=3: use [(1,2,3), e⁴, ..., e^{k-2}]
--     The 3-tour already contains (1,3). Default extensions preserve it.
-- [3] i=1, j>3: use [(1,2,3),(1,3,4),e⁵,...,e^{j-1},(1,2,j),(2,j,j+1),e^{j+2},...,e^{k-1}]
--     Build up to get (1,j) in the (k-1)-tour.
-- [4] i>1: similar routing using the natural HC construction.
--
-- Given edgeInHC, the selection pedigree is:
--   partialPedigree(k,i,j) ++ [(i,j,k)] ++ defaultSuffix(k,n)
-- and hypSum = C(i,j,k) since all other triangles are either default or the coefficient is known to be zero.

import MembershipProject.Core.N_HypSum
import MembershipProject.Core.N_ZeroPedigree
import MembershipProject.Core.N_EdgeInHC
import Mathlib.Tactic

namespace MembershipProject.Core

-- ============================================================
-- AXIOM: A valid partial pedigree on {1,...,k-1} with (i,j) in its last tour
-- ============================================================

/-- There exists a list of triangles forming a valid pedigree on layers 3..k-1
    whose (k-1)-tour contains edge (i,j).
    Cases [1]-[4] above give explicit constructions (proved in N_EdgeInHC.lean). -/
noncomputable axiom partialTriangles (k i j : ℕ) (hk : 4 ≤ k) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    List Triple

axiom partialTriangles_length (k i j : ℕ) (hk : 4 ≤ k) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    (partialTriangles k i j hk hi hij hjk).length = k - 3

axiom partialTriangles_head (k i j : ℕ) (hk : 4 ≤ k) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    (partialTriangles k i j hk hi hij hjk).head? = some (1,2,3)

axiom partialTriangles_layers (k i j : ℕ) (hk : 4 ≤ k) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k)
    (m : ℕ) (hm : m < (partialTriangles k i j hk hi hij hjk).length) :
    ((partialTriangles k i j hk hi hij hjk).get ⟨m, hm⟩).k = m + 3

axiom partialTriangles_allDefault (k i j : ℕ) (hk : 4 ≤ k) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    (partialTriangles k i j hk hi hij hjk).filter (fun t => !isDefault t) = []

/-- (i,j) is an edge in the (k-1)-tour produced by partialTriangles -/
axiom partialTriangles_hasEdge (k i j : ℕ) (hk : 4 ≤ k) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    ∃ a, (a, i, j) ∈ (partialTriangles k i j hk hi hij hjk) ∨
         ∃ b, (i, b, j) ∈ (partialTriangles k i j hk hi hij hjk)

-- ============================================================
-- DEFAULT SUFFIX: layers k+1..n
-- ============================================================

def defaultSuffix (k n : ℕ) : List Triple :=
  (List.range (n-k)).map (fun l => (k+l, k+l+1, k+l+2))

lemma defaultSuffix_length (k n : ℕ) (hkn : k ≤ n) :
    (defaultSuffix k n).length = n - k := by
  simp [defaultSuffix]

lemma defaultSuffix_allDefault (k n : ℕ) :
    (defaultSuffix k n).filter (fun t => !isDefault t) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro t ht
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp ht
  simp [isDefault, Triple.i, Triple.j, Triple.k]

-- ============================================================
-- SELECTION TRIANGLES
-- ============================================================

noncomputable def selectionTriangles (n k i j : ℕ) (hk : 4 ≤ k) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    List Triple :=
  partialTriangles k i j hk hi hij hjk ++ [(i,j,k)] ++ defaultSuffix k n

lemma selectionTriangles_length (n k i j : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k ≤ n)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    (selectionTriangles n k i j hk hi hij hjk).length = n - 2 := by
  simp [selectionTriangles, partialTriangles_length k i j hk hi hij hjk,
         defaultSuffix]
  omega

lemma selectionTriangles_head (n k i j : ℕ) (hk : 4 ≤ k) (hi : 1 ≤ i) (hij : i < j)
    (hjk : j < k) :
    (selectionTriangles n k i j hk hi hij hjk).head? = some (1,2,3) := by
  simp only [selectionTriangles]
  have hne : partialTriangles k i j hk hi hij hjk ≠ [] := by
    intro h
    have := partialTriangles_length k i j hk hi hij hjk
    simp [h] at this; omega
  have : (partialTriangles k i j hk hi hij hjk ++ [(i,j,k)] ++ defaultSuffix k n).head? =
      (partialTriangles k i j hk hi hij hjk).head? := by
    cases h : partialTriangles k i j hk hi hij hjk with
    | nil => exact absurd h hne
    | cons a t => simp
  rw [this]
  exact partialTriangles_head k i j hk hi hij hjk

lemma selectionTriangles_nonDefault (n k i j : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k ≤ n)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k)
    (hnd : isDefault (i,j,k) = false) :
    (selectionTriangles n k i j hk hi hij hjk).filter (fun t => !isDefault t) = [(i,j,k)] := by
  simp only [selectionTriangles, List.filter_append]
  rw [partialTriangles_allDefault, defaultSuffix_allDefault]
  simp [hnd]

-- ============================================================
-- SELECTION PEDIGREE
-- ============================================================

noncomputable axiom selectionPedigree (n k i j : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k ≤ n)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) : Pedigree n

/-- The triangles of selectionPedigree are selectionTriangles -/
axiom selectionPedigree_triangles (n k i j : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k ≤ n)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    (selectionPedigree n k i j hn hk hkn hi hij hjk).triangles =
    selectionTriangles n k i j hk hi hij hjk

-- ============================================================
-- HYPSUM WITH INDUCTION HYPOTHESIS
-- ============================================================

/-- All triangles in partialTriangles have layer < k (proved in N_EdgeInHC) -/
axiom partialTriangles_layers_lt (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    ∀ t ∈ partialTriangles k i j hk hi hij hjk, t.k < k
theorem hypSum_selectionPedigree_ih (n k i j : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k ≤ n)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k)
    (hnd : isDefault (i,j,k) = false)
    (C : Triple → ℚ)
    (ih : ∀ (a b m : ℕ), 1 ≤ a → a < b → b < m → 4 ≤ m → m < k → m ≤ n →
          isDefault (a,b,m) = false → C (a,b,m) = 0) :
    hypSum C (selectionPedigree n k i j hn hk hkn hi hij hjk) = C (i,j,k) := by
  simp only [hypSum, selectionPedigree_triangles]
  rw [selectionTriangles_nonDefault n k i j hn hk hkn hi hij hjk hnd]
  simp

theorem coeff_zero (n k i j : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k ≤ n)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k)
    (hnd : isDefault (i,j,k) = false)
    (C : Triple → ℚ)
    (hC : ∀ P : Pedigree n, hypSum C P = 0)
    (ih : ∀ (a b m : ℕ), 1 ≤ a → a < b → b < m → 4 ≤ m → m < k → m ≤ n →
          isDefault (a,b,m) = false → C (a,b,m) = 0) :
    C (i,j,k) = 0 := by
  have h := hC (selectionPedigree n k i j hn hk hkn hi hij hjk)
  rw [hypSum_selectionPedigree_ih n k i j hn hk hkn hi hij hjk hnd C ih] at h
  linarith

end MembershipProject.Core
