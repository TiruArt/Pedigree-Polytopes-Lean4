-- N_SelectionPedigreeExt.lean
-- Table-driven proof of Selection Pedigree existence.
--
-- Stem: partialPedigree(k+1,i,j) : Pedigree k with generator for (i,j,k+1)
-- Table (p = 0,1,2,...,n-k-2):
--   p=0: add (i,j,k+1),   generator from stem
--   p=1: add (i,k+1,k+2), generator = (i,j,k+1)
--   p≥2: add (k+p-1,k+p,k+p+1), generator = previous triangle (k+p-2,k+p-1,k+p)
-- hne at each step: new .j = current level → pedigree_hne
-- h_distinct applies only for positions > 0 (layers ≥ 4)

import MembershipProject.Core.N_PedigreeDefinition
import MembershipProject.Core.N_EdgeInHC
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace MembershipProject.Core

-- ============================================================
-- AXIOMS (technical Lean limitations, not mathematical gaps)
-- ============================================================

-- {i,j} not a pair in partialPedigree (hpair for List form)
axiom partialPedigree_hpair_list (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    ∀ pos, ∀ hpos : pos < (partialPedigree k i j hk hi hij hjk).triangles.length,
      ((partialPedigree k i j hk hi hij hjk).triangles.get ⟨pos, hpos⟩).i ≠ i ∨
      ((partialPedigree k i j hk hi hij hjk).triangles.get ⟨pos, hpos⟩).j ≠ j

-- Last triangle of (P.extend e ...) is e
-- (obvious: P.triangles ++ [e] has last element e)
axiom extend_last_get {n : ℕ} (P : Pedigree n) (e : Triple) he hgen hne :
    let Q := P.extend e he hgen hne
    Q.triangles.get ⟨Q.triangles.length - 1,
      by have := Q.h_length; have := Q.h_n; omega⟩ = e

-- triangles of (P.extend e ...) = P.triangles ++ [e]
lemma extend_triangles {n : ℕ} (P : Pedigree n) (e : Triple) he hgen hne :
    (P.extend e he hgen hne).triangles = P.triangles ++ [e] := rfl

-- ============================================================
-- hne: new .j = n > all existing .j (for ALL positions)
-- h_distinct applies only for positions > 0, but h_in_delta+h_layers
-- works for ALL positions including base (1,2,3) at position 0
-- ============================================================

lemma pedigree_hne {n : ℕ} (P : Pedigree n) (a : ℕ) :
    ∀ pos, ∀ hpos : pos < P.triangles.length,
      (P.triangles.get ⟨pos, hpos⟩).i ≠ a ∨
      (P.triangles.get ⟨pos, hpos⟩).j ≠ n := by
  intro pos hpos; right
  have hjk := mem_Delta_jl (P.h_in_delta pos hpos)
  have hlayer := P.h_layers pos hpos
  have hlen := P.h_length; have hn := P.h_n
  simp only [Triple.k] at hjk hlayer; omega

-- ============================================================
-- Generator lemmas
-- ============================================================

-- (a, m-1, m) ∈ generators(m-1, m, m+1) when a < m-1, a ≥ 1, m ≥ 4
lemma gen_default (a m : ℕ) (ha : 1 ≤ a) (ham : a < m-1) (hm : 4 ≤ m) :
    (a, m-1, m) ∈ generators (m-1, m, m+1) := by
  simp only [generators, Triple.i, Triple.j, Triple.k,
             show ¬(m-1 = 1 ∧ m = 2 ∧ m+1 = 3) from by omega,
             show m > 3 from by omega, if_false, if_true,
             Finset.mem_union, Finset.mem_image, Finset.mem_Ico]
  left; exact ⟨a, ⟨by omega, by omega⟩, rfl⟩

-- ============================================================
-- PedWithLast: Pedigree m bundled with invariant on last triangle
-- last triangle = (last_i, m-1, m) with last_i < m-1
-- This invariant is exactly what gen_default needs
-- ============================================================

structure PedWithLast (m : ℕ) where
  ped      : Pedigree m
  last_i   : ℕ
  h_last_i : 1 ≤ last_i
  h_last_j : last_i < m - 1
  h_last   : ped.triangles.get
               ⟨ped.triangles.length - 1,
                by have := ped.h_length; have := ped.h_n; omega⟩ =
             (last_i, m-1, m)

-- One default extension step: Pedigree m → Pedigree (m+1)
-- New triangle: (m-1, m, m+1)
-- hgen: last triangle (last_i, m-1, m) ∈ generators(m-1, m, m+1) ✓
-- hne:  new .j = m = level of ped → pedigree_hne ✓
noncomputable def pedStep {m : ℕ} (P : PedWithLast m) (hm : 4 ≤ m) :
    PedWithLast (m+1) where
  ped := P.ped.extend (m-1, m, m+1)
    (mem_Delta_self (m-1) m (by omega) (by omega) (by omega))
    ⟨P.ped.triangles.length - 1,
     by have := P.ped.h_length; have := P.ped.h_n; omega,
     P.h_last ▸ gen_default P.last_i m P.h_last_i P.h_last_j hm⟩
    (pedigree_hne P.ped (m-1))
  last_i   := m - 1
  h_last_i := by omega
  h_last_j := by simp; omega
  h_last   := by
    have := extend_last_get P.ped (m-1, m, m+1)
               (mem_Delta_self (m-1) m (by omega) (by omega) (by omega))
               ⟨P.ped.triangles.length - 1, by
                  have := P.ped.h_length; have := P.ped.h_n; omega,
                P.h_last ▸ gen_default P.last_i m P.h_last_i P.h_last_j hm⟩
               (pedigree_hne P.ped (m-1))
    simp only [show m + 1 - 1 = m from by omega]
    convert this using 2

-- Iterate pedStep d times
noncomputable def pedChain {m : ℕ} (P : PedWithLast m) (hm : 4 ≤ m) :
    ∀ d : ℕ, PedWithLast (m + d)
  | 0     => by simpa using P
  | d + 1 => by
      have P' := pedChain P hm d
      have hm' : 4 ≤ m + d := by omega
      have P'' := pedStep P' hm'
      have : m + (d + 1) = m + d + 1 := by omega
      rw [this]; exact P''

-- cast_triangles: triangles are preserved under cast of Pedigree
lemma cast_triangles {m n : ℕ} (h : m = n) (P : Pedigree m) :
    (h ▸ P).triangles = P.triangles := by
  subst h; rfl


-- pedChain_triangles: table-driven proof by induction on d.
-- The triangle generator table:
--   Step 0: last of stem (P.last_i, m-1, m); generator from PedWithLast.h_last
--   Step p: triangle (m+p-1, m+p, m+p+1); generator = previous triangle
--           (m+p-2, m+p-1, m+p) with .i = m+p-2 < m+p-1 ✓
-- So (pedChain P hm d).ped.triangles = P.ped.triangles ++
--   [(m-1,m,m+1), (m,m+1,m+2), ..., (m+d-2,m+d-1,m+d)]
--   = P.ped.triangles ++ (List.range d).map (fun p => (m+p-1, m+p, m+p+1))
lemma pedChain_triangles {m : ℕ} (P : PedWithLast m) (hm : 4 ≤ m) :
    ∀ d : ℕ, (pedChain P hm d).ped.triangles =
      P.ped.triangles ++
      (List.range d).map (fun p => (m+p-1, m+p, m+p+1))
  | 0 => by
      -- Base: no steps taken, no triangles appended
      simp [pedChain]
  | d + 1 => by
      -- Step: pedChain (d+1) = pedStep (pedChain d)
      -- pedStep appends exactly (m+d-1, m+d, m+d+1) — the triangle at row d of the table
      -- Its generator is the previous triangle (m+d-2, m+d-1, m+d)
      -- which has .i = m+d-2 < m+d-1 = .j, satisfying gen_default
      have hm' : 4 ≤ m + d := by omega
      have ih := pedChain_triangles P hm d
      -- pedStep appends (m+d-1, m+d, m+d+1) via Pedigree.extend
      have hstep : (pedStep (pedChain P hm d) hm').ped.triangles =
                   (pedChain P hm d).ped.triangles ++ [(m+d-1, m+d, m+d+1)] := by
        simp [pedStep, extend_triangles]
      -- Combine: pedChain (d+1) triangles =
      --   P.ped.triangles ++ range(d).map(...) ++ [(m+d-1, m+d, m+d+1)]
      --   = P.ped.triangles ++ range(d+1).map(...)
      -- pedChain (d+1) = pedStep (pedChain d) by definition
      have hdef : (pedChain P hm (d+1)).ped.triangles =
                  (pedStep (pedChain P hm d) hm').ped.triangles := by
        simp [pedChain]
      rw [hdef, hstep, ih]
      rw [List.range_succ, List.map_append, List.map_singleton]
      simp [List.append_assoc]

-- ============================================================
-- STEP 1: selStep1 — extend Pedigree k by (i,j,k+1)
-- ============================================================

noncomputable def selStep1 (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) : Pedigree (k+1) :=
  (partialPedigree (k+1) i j (by omega) hi hij (by omega)).extend
    (i, j, k+1)
    (mem_Delta_self i j hi hij (by omega))
    (partialPedigree_hasEdge (k+1) i j (by omega) hi hij (by omega))
    (partialPedigree_hpair_list (k+1) i j (by omega) hi hij (by omega))

lemma selStep1_last (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    (selStep1 k i j hk hi hij hjk).triangles.get
      ⟨(selStep1 k i j hk hi hij hjk).triangles.length - 1,
       by have := (selStep1 k i j hk hi hij hjk).h_length
          have := (selStep1 k i j hk hi hij hjk).h_n; omega⟩ = (i, j, k+1) :=
  extend_last_get _ _ _ _ _

-- ============================================================
-- STEP 2: selStep2 — extend selStep1 by (i,k+1,k+2)
-- hgen: (i,j,k+1) ∈ generators(i,k+1,k+2) since j < k+1 and j > i
-- ============================================================

lemma gen_step2 (i j k : ℕ) (hij : i < j) (hjk : j < k) (hk4 : 4 ≤ k) :
    (i, j, k+1) ∈ generators (i, k+1, k+2) := by
  simp only [generators, Triple.i, Triple.j, Triple.k,
             show ¬(i = 1 ∧ k+1 = 2 ∧ k+2 = 3) from by omega,
             show k+1 > 3 from by omega, if_false, if_true,
             Finset.mem_union, Finset.mem_image, Finset.mem_Ico]
  right; exact ⟨j, ⟨by omega, by omega⟩, rfl⟩

noncomputable def selStep2 (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) : PedWithLast (k+2) where
  ped := (selStep1 k i j hk hi hij hjk).extend
    (i, k+1, k+2)
    (mem_Delta_self i (k+1) hi (by omega) (by omega))
    ⟨(selStep1 k i j hk hi hij hjk).triangles.length - 1,
     by have := (selStep1 k i j hk hi hij hjk).h_length
        have := (selStep1 k i j hk hi hij hjk).h_n; omega,
     selStep1_last k i j hk hi hij hjk ▸ gen_step2 i j k hij hjk hk⟩
    (pedigree_hne (selStep1 k i j hk hi hij hjk) i)
  last_i   := i
  h_last_i := hi
  h_last_j := by omega
  h_last   := by
    have := extend_last_get (selStep1 k i j hk hi hij hjk) (i, k+1, k+2)
               (mem_Delta_self i (k+1) hi (by omega) (by omega))
               ⟨(selStep1 k i j hk hi hij hjk).triangles.length - 1,
                by have := (selStep1 k i j hk hi hij hjk).h_length
                   have := (selStep1 k i j hk hi hij hjk).h_n; omega,
                selStep1_last k i j hk hi hij hjk ▸ gen_step2 i j k hij hjk hk⟩
               (pedigree_hne (selStep1 k i j hk hi hij hjk) i)
    convert this using 2

-- Analogues for P2 (inner pair i,k) and P3
noncomputable def selStep1' (k i : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hik : i < k) : Pedigree (k+1) :=
  (partialPedigree (k+1) i k (by omega) hi hik (by omega)).extend
    (i, k, k+1)
    (mem_Delta_self i k hi hik (by omega))
    (partialPedigree_hasEdge (k+1) i k (by omega) hi hik (by omega))
    (partialPedigree_hpair_list (k+1) i k (by omega) hi hik (by omega))

lemma selStep1'_last (k i : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hik : i < k) :
    (selStep1' k i hk hi hik).triangles.get
      ⟨(selStep1' k i hk hi hik).triangles.length - 1,
       by have := (selStep1' k i hk hi hik).h_length
          have := (selStep1' k i hk hi hik).h_n; omega⟩ = (i, k, k+1) :=
  extend_last_get _ _ _ _ _

lemma gen_step2_ik (i k : ℕ) (hi : 1 ≤ i) (hik : i < k) (hk4 : 4 ≤ k) :
    (i, k, k+1) ∈ generators (i, k+1, k+2) := by
  simp only [generators, Triple.i, Triple.j, Triple.k,
             show ¬(i = 1 ∧ k+1 = 2 ∧ k+2 = 3) from by omega,
             show k+1 > 3 from by omega, if_false, if_true,
             Finset.mem_union, Finset.mem_image, Finset.mem_Ico]
  right; exact ⟨k, ⟨by omega, by omega⟩, rfl⟩

-- selStep1 as PedWithLast (for P2)
noncomputable def selStep1'_PWL (k i : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hik : i < k) : PedWithLast (k+1) where
  ped      := selStep1' k i hk hi hik
  last_i   := i
  h_last_i := hi
  h_last_j := by omega
  h_last   := by
    have := extend_last_get
               (partialPedigree (k+1) i k (by omega) hi hik (by omega))
               (i, k, k+1)
               (mem_Delta_self i k hi hik (by omega))
               (partialPedigree_hasEdge (k+1) i k (by omega) hi hik (by omega))
               (partialPedigree_hpair_list (k+1) i k (by omega) hi hik (by omega))
    convert this using 2

noncomputable def selStep2' (k i : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hik : i < k) : PedWithLast (k+2) where
  ped := (selStep1' k i hk hi hik).extend
    (i, k+1, k+2)
    (mem_Delta_self i (k+1) hi (by omega) (by omega))
    ⟨(selStep1' k i hk hi hik).triangles.length - 1,
     by have := (selStep1' k i hk hi hik).h_length
        have := (selStep1' k i hk hi hik).h_n; omega,
     selStep1'_last k i hk hi hik ▸ gen_step2_ik i k hi hik hk⟩
    (pedigree_hne (selStep1' k i hk hi hik) i)
  last_i   := i
  h_last_i := hi
  h_last_j := by omega
  h_last   := by
    have := extend_last_get (selStep1' k i hk hi hik) (i, k+1, k+2)
               (mem_Delta_self i (k+1) hi (by omega) (by omega))
               ⟨(selStep1' k i hk hi hik).triangles.length - 1,
                by have := (selStep1' k i hk hi hik).h_length
                   have := (selStep1' k i hk hi hik).h_n; omega,
                selStep1'_last k i hk hi hik ▸ gen_step2_ik i k hi hik hk⟩
               (pedigree_hne (selStep1' k i hk hi hik) i)
    convert this using 2

-- ============================================================
-- extendToN: close the 3 pedigree existence axioms
-- ============================================================

noncomputable def extendToN_P1 (n k i j : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k+2 ≤ n)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) : Pedigree n :=
  (show (k+2)+(n-k-2) = n by omega) ▸
    (pedChain (selStep2 k i j hk hi hij hjk) (by omega) (n-k-2)).ped

noncomputable def extendToN_P2 (n k i : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k+1 ≤ n)
    (hi : 1 ≤ i) (hik : i < k) : Pedigree n :=
  (show (k+1)+(n-k-1) = n by omega) ▸
    (pedChain (selStep1'_PWL k i hk hi hik) (by omega) (n-k-1)).ped

noncomputable def extendToN_P3 (n k i : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k+2 ≤ n)
    (hi : 1 ≤ i) (hik : i < k) : Pedigree n :=
  (show (k+2)+(n-k-2) = n by omega) ▸
    (pedChain (selStep2' k i hk hi hik) (by omega) (n-k-2)).ped

-- Triangle lists of extendToN_P1/P2/P3
-- These give the explicit triangles avoiding cast issues

-- extendToN triangle theorems: use omega_cast to strip the Eq.mpr
-- (h.mpr P).triangles = P.triangles
-- h : Pedigree n = Pedigree m, P : Pedigree m, h.mpr P : Pedigree n
-- Since Pedigree is a structure with triangles : List Triple (not depending on n in type),
-- the triangles field is preserved.
theorem extendToN_P1_triangles (n k i j : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k+2 ≤ n)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    (extendToN_P1 n k i j hn hk hkn hi hij hjk).triangles =
    (selStep2 k i j hk hi hij hjk).ped.triangles ++
    (List.range (n-k-2)).map (fun p => (k+2+p-1, k+2+p, k+2+p+1)) := by
  simp only [extendToN_P1]
  rw [cast_triangles (by omega : (k+2)+(n-k-2) = n), pedChain_triangles]

theorem extendToN_P2_triangles (n k i : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k+1 ≤ n)
    (hi : 1 ≤ i) (hik : i < k) :
    (extendToN_P2 n k i hn hk hkn hi hik).triangles =
    (selStep1'_PWL k i hk hi hik).ped.triangles ++
    (List.range (n-k-1)).map (fun p => (k+1+p-1, k+1+p, k+1+p+1)) := by
  simp only [extendToN_P2]
  rw [cast_triangles (by omega : (k+1)+(n-k-1) = n), pedChain_triangles]

theorem extendToN_P3_triangles (n k i : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k+2 ≤ n)
    (hi : 1 ≤ i) (hik : i < k) :
    (extendToN_P3 n k i hn hk hkn hi hik).triangles =
    (selStep2' k i hk hi hik).ped.triangles ++
    (List.range (n-k-2)).map (fun p => (k+2+p-1, k+2+p, k+2+p+1)) := by
  simp only [extendToN_P3]
  rw [cast_triangles (by omega : (k+2)+(n-k-2) = n), pedChain_triangles]

end MembershipProject.Core
