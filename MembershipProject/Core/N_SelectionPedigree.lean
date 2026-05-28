-- N_SelectionPedigree.lean
-- Selection Lemma (Chapter 7): Three pedigrees prove C(i,j,k+1) = 0.
-- All 6 selectionPedigree axioms closed by N_SelectionPedigreeExt.
--
-- P1: partial(k+1,i,j) ++ [(i,j,k+1),(i,k+1,k+2)] ++ def(k+3..n)
-- P2: partial(k+1,i,k) ++ [(i,k,k+1)]              ++ def(k+2..n)
-- P3: partial(k+1,i,k) ++ [(i,k,k+1),(i,k+1,k+2)] ++ def(k+3..n)
-- IH: C(a,b,m)=0 for m ≤ k. P2+P3 → C(i,k+1,k+2)=0. P1 → C(i,j,k+1)=0.

import MembershipProject.Core.N_HypSum
import MembershipProject.Core.N_ZeroPedigree
import MembershipProject.Core.N_EdgeInHC
import MembershipProject.Core.N_SelectionPedigreeExt
import Mathlib.Tactic

namespace MembershipProject.Core

-- triangles are preserved under heterogeneous cast of Pedigree
private lemma pedigree_cast_triangles {m n : ℕ} (h : m = n) (P : Pedigree m) :
    (h ▸ P).triangles = P.triangles := by subst h; rfl

-- ============================================================
-- PARTIAL TRIANGLES: Pedigree k — layers 3..k — k-tour has (i,j)
-- Defined from partialPedigree (k+1) i j : Pedigree k
-- ============================================================

noncomputable def partialTriangles (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) : List Triple :=
  (partialPedigree (k+1) i j (by omega) hi hij (by omega)).triangles

lemma partialTriangles_length (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    (partialTriangles k i j hk hi hij hjk).length = k - 2 := by
  simp only [partialTriangles]
  have h  := (partialPedigree (k+1) i j (by omega) hi hij (by omega)).h_length
  have hn := (partialPedigree (k+1) i j (by omega) hi hij (by omega)).h_n
  omega

lemma partialTriangles_layers_le (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    ∀ t ∈ partialTriangles k i j hk hi hij hjk, t.k ≤ k := by
  intro t ht
  simp only [partialTriangles] at ht
  exact Nat.lt_succ_iff.mp
    (partialPedigree_layers_lt (k+1) i j (by omega) hi hij (by omega) t ht)

-- ============================================================
-- DEFAULT SUFFIXES (pure addition, no ℕ subtraction)
-- def2: layers k+2..n (for P2)
-- def3: layers k+3..n (for P1, P3)
-- ============================================================

def defaultSuffix2 (k n : ℕ) : List Triple :=
  (List.range (n - k - 1)).map (fun p => (k+p, k+p+1, k+p+2))

def defaultSuffix3 (k n : ℕ) : List Triple :=
  (List.range (n - k - 2)).map (fun p => (k+p+1, k+p+2, k+p+3))

lemma defaultSuffix2_allDefault (k n : ℕ) :
    (defaultSuffix2 k n).filter (fun t => !isDefault t) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro t ht
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp ht
  simp [isDefault, Triple.i, Triple.j, Triple.k]

lemma defaultSuffix3_allDefault (k n : ℕ) :
    (defaultSuffix3 k n).filter (fun t => !isDefault t) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro t ht
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp ht
  simp [isDefault, Triple.i, Triple.j, Triple.k]

-- ============================================================
-- THREE SELECTION TRIANGLE LISTS
-- ============================================================

noncomputable def selTriangles1 (n k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) : List Triple :=
  partialTriangles k i j hk hi hij hjk ++
  [(i, j, k+1), (i, k+1, k+2)] ++
  defaultSuffix3 k n

noncomputable def selTriangles2 (n k i : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hik : i < k) : List Triple :=
  (partialPedigree (k+1) i k (by omega) hi hik (by omega)).triangles ++
  [(i, k, k+1)] ++
  defaultSuffix2 k n

noncomputable def selTriangles3 (n k i : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hik : i < k) : List Triple :=
  (partialPedigree (k+1) i k (by omega) hi hik (by omega)).triangles ++
  [(i, k, k+1), (i, k+1, k+2)] ++
  defaultSuffix3 k n

-- ============================================================
-- SELECTION PEDIGREES: proved using N_SelectionPedigreeExt
-- ============================================================

noncomputable def selectionPedigree1 (n k i j : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k)
    (hkn : k+2 ≤ n) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) : Pedigree n :=
  extendToN_P1 n k i j hn hk hkn hi hij hjk

theorem selectionPedigree1_triangles (n k i j : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k)
    (hkn : k+2 ≤ n) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    (selectionPedigree1 n k i j hn hk hkn hi hij hjk).triangles =
    selTriangles1 n k i j hk hi hij hjk := by
  simp only [selectionPedigree1, selTriangles1, partialTriangles]
  -- extendToN_P1_triangles gives: extendToN_P1.triangles = selStep2.triangles ++ range.map
  have hP1 := extendToN_P1_triangles n k i j hn hk hkn hi hij hjk
  -- selStep2.triangles = partialPedigree.triangles ++ [(i,j,k+1),(i,k+1,k+2)]
  have hS2 : (selStep2 k i j hk hi hij hjk).ped.triangles =
      (partialPedigree (k+1) i j (by omega) hi hij (by omega)).triangles ++
      [(i, j, k+1), (i, k+1, k+2)] := by
    simp [selStep2, selStep1, extend_triangles, List.append_assoc]
  rw [hP1, hS2]
  congr 1
  apply List.map_congr_left; intro p
  simp only [Prod.mk.injEq]; omega

noncomputable def selectionPedigree2 (n k i : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k)
    (hkn : k+1 ≤ n) (hi : 1 ≤ i) (hik : i < k) : Pedigree n :=
  extendToN_P2 n k i hn hk hkn hi hik

theorem selectionPedigree2_triangles (n k i : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k)
    (hkn : k+1 ≤ n) (hi : 1 ≤ i) (hik : i < k) :
    (selectionPedigree2 n k i hn hk hkn hi hik).triangles =
    selTriangles2 n k i hk hi hik := by
  simp only [selectionPedigree2, selTriangles2]
  have hP2 := extendToN_P2_triangles n k i hn hk hkn hi hik
  have hS1 : (selStep1'_PWL k i hk hi hik).ped.triangles =
      (partialPedigree (k+1) i k (by omega) hi hik (by omega)).triangles ++
      [(i, k, k+1)] := by
    simp [selStep1'_PWL, selStep1', extend_triangles]
  rw [hP2, hS1]
  congr 1
  apply List.map_congr_left; intro p
  simp only [Prod.mk.injEq]; omega

noncomputable def selectionPedigree3 (n k i : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k)
    (hkn : k+2 ≤ n) (hi : 1 ≤ i) (hik : i < k) : Pedigree n :=
  extendToN_P3 n k i hn hk hkn hi hik

theorem selectionPedigree3_triangles (n k i : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k)
    (hkn : k+2 ≤ n) (hi : 1 ≤ i) (hik : i < k) :
    (selectionPedigree3 n k i hn hk hkn hi hik).triangles =
    selTriangles3 n k i hk hi hik := by
  simp only [selectionPedigree3, selTriangles3]
  have hP3 := extendToN_P3_triangles n k i hn hk hkn hi hik
  have hS2 : (selStep2' k i hk hi hik).ped.triangles =
      (partialPedigree (k+1) i k (by omega) hi hik (by omega)).triangles ++
      [(i, k, k+1), (i, k+1, k+2)] := by
    simp [selStep2', selStep1', extend_triangles, List.append_assoc]
  rw [hP3, hS2]
  congr 1
  apply List.map_congr_left; intro p
  simp only [Prod.mk.injEq]; omega

-- ============================================================
-- KEY LEMMA: partial triangles contribute 0 to hypSum via IH
-- ============================================================

lemma partialPed_sum_zero (k i j : ℕ) (hk : 5 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k)
    (C : Triple → ℚ)
    (ih : ∀ a b m, 1 ≤ a → a < b → b < m → 4 ≤ m → m ≤ k-1 →
          isDefault (a,b,m) = false → C (a,b,m) = 0) :
    ((partialPedigree k i j (by omega) hi hij (by omega)).triangles.filter
      (fun t => !isDefault t) |>.map C).sum = 0 := by
  apply List.sum_eq_zero
  intro c hc
  simp only [List.mem_map] at hc
  obtain ⟨t, ht_filter, rfl⟩ := hc
  simp only [List.mem_filter] at ht_filter
  obtain ⟨ht_mem, ht_nd⟩ := ht_filter
  obtain ⟨⟨m, hm⟩, hmt⟩ := List.mem_iff_get.mp ht_mem
  have hlayer := (partialPedigree k i j (by omega) hi hij (by omega)).h_layers m hm
  simp only [Triple.k] at hlayer
  have htkeq : t.2.2 = m + 3 := by rw [← hmt]; exact hlayer
  have hlen := (partialPedigree k i j (by omega) hi hij (by omega)).h_length
  have hn'  := (partialPedigree k i j (by omega) hi hij (by omega)).h_n
  have htk : t.2.2 ≤ k - 1 := by omega
  have htk4 : 4 ≤ t.2.2 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · exfalso
      have hfirst := (partialPedigree k i j (by omega) hi hij (by omega)).h_first
      cases htl : (partialPedigree k i j (by omega) hi hij (by omega)).triangles with
      | nil => simp [htl] at hm
      | cons hd tl =>
        simp only [htl] at hfirst
        have hhd : hd = (1,2,3) := Option.some.inj hfirst
        have hget : (partialPedigree k i j (by omega) hi hij (by omega)).triangles.get ⟨0, hm⟩ = hd := by
          simp [htl]
        have : t = (1,2,3) := by rw [← hmt, hget, hhd]
        rw [this] at ht_nd; simp [isDefault, Triple.i, Triple.j, Triple.k] at ht_nd
    · omega
  have hdelta := (partialPedigree k i j (by omega) hi hij (by omega)).h_in_delta m hm
  rw [hmt] at hdelta
  have hnd : isDefault t = false := by
    cases h : isDefault t
    · rfl
    · simp [h] at ht_nd
  have hCt := ih t.i t.j t.k
    (mem_Delta_i1 hdelta) (mem_Delta_ij hdelta) (mem_Delta_jl hdelta)
    (by simp [Triple.k]; exact htk4)
    (by simp [Triple.k]; exact htk)
    (by simp [isDefault, Triple.i, Triple.j, Triple.k] at hnd ⊢; tauto)
  simp only [Triple.i, Triple.j, Triple.k] at hCt
  exact hCt

-- ============================================================
-- HYPSUM OF EACH SELECTION PEDIGREE
-- ============================================================

theorem hypSum_P1 (n k i j : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k+2 ≤ n)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k)
    (hnd1 : isDefault (i,j,k+1) = false)
    (hnd2 : isDefault (i,k+1,k+2) = false)
    (C : Triple → ℚ)
    (ih : ∀ a b m, 1 ≤ a → a < b → b < m → 4 ≤ m → m ≤ k →
          isDefault (a,b,m) = false → C (a,b,m) = 0) :
    hypSum C (selectionPedigree1 n k i j hn hk hkn hi hij hjk) =
    C (i,j,k+1) + C (i,k+1,k+2) := by
  simp only [hypSum, selectionPedigree1_triangles, selTriangles1, partialTriangles]
  simp only [List.filter_append, List.map_append, List.sum_append]
  rw [defaultSuffix3_allDefault]; simp only [List.map_nil, List.sum_nil, add_zero]
  simp only [List.filter_cons, hnd1, hnd2, Bool.not_false, List.filter_nil,
             if_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h := partialPed_sum_zero (k+1) i j (by omega) hi hij (by omega) C
    (fun a b m ha hab hbm hm4 hmk hnd => ih a b m ha hab hbm hm4 (by omega) hnd)
  linarith

theorem hypSum_P2 (n k i : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k+1 ≤ n)
    (hi : 1 ≤ i) (hik : i < k)
    (hnd : isDefault (i,k,k+1) = false)
    (C : Triple → ℚ)
    (ih : ∀ a b m, 1 ≤ a → a < b → b < m → 4 ≤ m → m ≤ k →
          isDefault (a,b,m) = false → C (a,b,m) = 0) :
    hypSum C (selectionPedigree2 n k i hn hk hkn hi hik) = C (i,k,k+1) := by
  simp only [hypSum, selectionPedigree2_triangles, selTriangles2]
  simp only [List.filter_append, List.map_append, List.sum_append]
  rw [defaultSuffix2_allDefault]; simp only [List.map_nil, List.sum_nil, add_zero]
  simp only [List.filter_cons, hnd, Bool.not_false, List.filter_nil,
             if_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h := partialPed_sum_zero (k+1) i k (by omega) hi hik (by omega) C
    (fun a b m ha hab hbm hm4 hmk hnd => ih a b m ha hab hbm hm4 (by omega) hnd)
  linarith

theorem hypSum_P3 (n k i : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k+2 ≤ n)
    (hi : 1 ≤ i) (hik : i < k)
    (hnd1 : isDefault (i,k,k+1) = false)
    (hnd2 : isDefault (i,k+1,k+2) = false)
    (C : Triple → ℚ)
    (ih : ∀ a b m, 1 ≤ a → a < b → b < m → 4 ≤ m → m ≤ k →
          isDefault (a,b,m) = false → C (a,b,m) = 0) :
    hypSum C (selectionPedigree3 n k i hn hk hkn hi hik) =
    C (i,k,k+1) + C (i,k+1,k+2) := by
  simp only [hypSum, selectionPedigree3_triangles, selTriangles3]
  simp only [List.filter_append, List.map_append, List.sum_append]
  rw [defaultSuffix3_allDefault]; simp only [List.map_nil, List.sum_nil, add_zero]
  simp only [List.filter_cons, hnd1, hnd2, Bool.not_false, List.filter_nil,
             if_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h := partialPed_sum_zero (k+1) i k (by omega) hi hik (by omega) C
    (fun a b m ha hab hbm hm4 hmk hnd => ih a b m ha hab hbm hm4 (by omega) hnd)
  linarith

-- ============================================================
-- MAIN THEOREM: C(i,j,k+1) = 0
-- ============================================================

theorem coeff_zero (n k i j : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k+2 ≤ n)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k)
    (hnd : isDefault (i,j,k+1) = false)
    (C : Triple → ℚ)
    (hC : ∀ P : Pedigree n, hypSum C P = 0)
    (ih : ∀ a b m, 1 ≤ a → a < b → b < m → 4 ≤ m → m ≤ k →
          isDefault (a,b,m) = false → C (a,b,m) = 0) :
    C (i,j,k+1) = 0 := by
  have hnd_ik  : isDefault (i,k,k+1)   = false := by
    simp [isDefault, Triple.i, Triple.j, Triple.k]; omega
  have hnd_ik2 : isDefault (i,k+1,k+2) = false := by
    simp [isDefault, Triple.i, Triple.j, Triple.k]; omega
  have hP1 := hC (selectionPedigree1 n k i j hn hk hkn hi hij hjk)
  rw [hypSum_P1 n k i j hn hk hkn hi hij hjk hnd hnd_ik2 C ih] at hP1
  have hP2 := hC (selectionPedigree2 n k i hn hk (by omega) hi (by omega))
  rw [hypSum_P2 n k i hn hk (by omega) hi (by omega) hnd_ik C ih] at hP2
  have hP3 := hC (selectionPedigree3 n k i hn hk hkn hi (by omega))
  rw [hypSum_P3 n k i hn hk hkn hi (by omega) hnd_ik hnd_ik2 C ih] at hP3
  linarith

end MembershipProject.Core
