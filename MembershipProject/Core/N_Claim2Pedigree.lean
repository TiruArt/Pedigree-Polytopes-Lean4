-- N_Claim2Pedigrees.lean
-- Proves C(1,2,4) = 0 and C(1,3,4) = 0 using P1, P2, P3.

import MembershipProject.Core.N_HypSum
import MembershipProject.Core.N_ZeroPedigree
import Mathlib.Tactic

namespace MembershipProject.Core

-- ============================================================
-- P2: [(1,2,3),(1,3,4),(3,4,5),(4,5,6),...,(n-2,n-1,n)]
-- Only (1,3,4) is non-default → hypSum C P2 = C(1,3,4) = 0
-- ============================================================

def P2triangles (n : ℕ) : List Triple :=
  (1,2,3) :: (1,3,4) :: (List.range (n-4)).map (fun i => (i+3, i+4, i+5))

def pedigree_P2 (n : ℕ) (hn : 6 ≤ n) : Pedigree n where
  triangles    := P2triangles n
  h_n          := by omega
  h_length     := by simp [P2triangles]; omega
  h_first      := by simp [P2triangles]
  h_layers     := by
    intro i hi
    simp only [P2triangles]
    match i with
    | 0 => simp [Triple.k]
    | 1 => simp [Triple.k]
    | i+2 => simp [Triple.k]
  h_in_delta   := by
    intro i hi
    simp only [P2triangles]
    match i with
    | 0 => simp [mem_Delta_iff, Triple.i, Triple.j, Triple.k]
    | 1 => simp [mem_Delta_iff, Triple.i, Triple.j, Triple.k]
    | i+2 => simp [mem_Delta_iff, Triple.i, Triple.j, Triple.k]
  h_distinct   := by
    intro i j hi hj hipos hjpos hne
    simp only [P2triangles]
    match i, j with
    | 1, j+2 => simp [Triple.i, Triple.j]
    | i+2, 1 => simp [Triple.i, Triple.j]
    | i+2, j+2 => simp [Triple.i, Triple.j]; omega
    | 1, 1 => omega
  h_generators := by
    intro i hpos hi
    simp only [P2triangles]
    match i with
    | 0 => omega
    | 1 =>
      exact ⟨0, by omega, by
        simp [generators, Triple.i, Triple.j, Triple.k]⟩
    | 2 =>
      exact ⟨1, by omega, by
        simp [generators, Triple.i, Triple.j, Triple.k]⟩
    | i+3 =>
      exact ⟨i+2, by omega, by
        simp [generators, Triple.i, Triple.j, Triple.k]⟩

lemma hypSum_P2 (n : ℕ) (hn : 6 ≤ n) (C : Triple → ℚ) :
    hypSum C (pedigree_P2 n hn) = C (1,3,4) := by
  simp only [hypSum, pedigree_P2, P2triangles]
  have hnil : ((List.range (n-4)).map (fun i => (i + 3, i + 4, i + 5))).filter
      (fun t => !isDefault t) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
    simp [isDefault, Triple.i, Triple.j, Triple.k]
  have hfull : (P2triangles n).filter (fun t => !isDefault t) = [(1,3,4)] := by
    simp [P2triangles, isDefault, Triple.i, Triple.j, Triple.k]
  change (((P2triangles n).filter (fun t => !isDefault t)).map C).sum = C (1,3,4)
  rw [hfull]; simp

-- ============================================================
-- P1: [(1,2,3),(1,2,4),(1,4,5),(4,5,6),...,(n-2,n-1,n)]
-- Non-default: (1,2,4) and (1,4,5) → hypSum = C(1,2,4)+C(1,4,5) = 0
-- ============================================================

def P1triangles (n : ℕ) : List Triple :=
  (1,2,3) :: (1,2,4) :: (1,4,5) :: (List.range (n-5)).map (fun i => (i+4, i+5, i+6))

def pedigree_P1 (n : ℕ) (hn : 6 ≤ n) : Pedigree n where
  triangles    := P1triangles n
  h_n          := by omega
  h_length     := by simp [P1triangles]; omega
  h_first      := by simp [P1triangles]
  h_layers     := by
    intro i hi
    simp only [P1triangles]
    match i with
    | 0 => simp [Triple.k]
    | 1 => simp [Triple.k]
    | 2 => simp [Triple.k]
    | i+3 => simp [Triple.k]
  h_in_delta   := by
    intro i hi
    simp only [P1triangles]
    match i with
    | 0 => simp [mem_Delta_iff, Triple.i, Triple.j, Triple.k]
    | 1 => simp [mem_Delta_iff, Triple.i, Triple.j, Triple.k]
    | 2 => simp [mem_Delta_iff, Triple.i, Triple.j, Triple.k]
    | i+3 => simp [mem_Delta_iff, Triple.i, Triple.j, Triple.k]
  h_distinct   := by
    intro i j hi hj hipos hjpos hne
    simp only [P1triangles]
    match i, j with
    | 1, 2 => simp [Triple.i, Triple.j]
    | 2, 1 => simp [Triple.i, Triple.j]
    | 1, j+3 => simp [Triple.i, Triple.j]
    | j+3, 1 => simp [Triple.i, Triple.j]
    | 2, j+3 => simp [Triple.i, Triple.j]
    | j+3, 2 => simp [Triple.i, Triple.j]
    | i+3, j+3 => simp [Triple.i, Triple.j]; omega
    | 1, 1 => omega
    | 2, 2 => omega
  h_generators := by
    intro i hpos hi
    simp only [P1triangles]
    match i with
    | 0 => omega
    | 1 =>
      exact ⟨0, by omega, by simp [generators, Triple.i, Triple.j, Triple.k]⟩
    | 2 =>
      exact ⟨1, by omega, by
        simp [generators, Triple.i, Triple.j, Triple.k]⟩
    | 3 =>
      exact ⟨2, by omega, by
        simp [generators, Triple.i, Triple.j, Triple.k]⟩
    | i+4 =>
      exact ⟨i+3, by omega, by
        simp [generators, Triple.i, Triple.j, Triple.k]⟩

lemma hypSum_P1 (n : ℕ) (hn : 6 ≤ n) (C : Triple → ℚ) :
    hypSum C (pedigree_P1 n hn) = C (1,2,4) + C (1,4,5) := by
  simp only [hypSum, pedigree_P1, P1triangles]
  have hnil : ((List.range (n-5)).map (fun i => (i + 4, i + 5, i + 6))).filter
      (fun t => !isDefault t) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
    simp [isDefault, Triple.i, Triple.j, Triple.k]
  have hfull : (P1triangles n).filter (fun t => !isDefault t) = [(1,2,4), (1,4,5)] := by
    simp [P1triangles, isDefault, Triple.i, Triple.j, Triple.k]
  change (((P1triangles n).filter (fun t => !isDefault t)).map C).sum = C (1,2,4) + C (1,4,5)
  rw [hfull]; simp

-- ============================================================
-- P3: [(1,2,3),(1,3,4),(1,4,5),(4,5,6),...,(n-2,n-1,n)]
-- Non-default: (1,3,4) and (1,4,5) → hypSum = C(1,3,4)+C(1,4,5) = 0
-- ============================================================

def P3triangles (n : ℕ) : List Triple :=
  (1,2,3) :: (1,3,4) :: (1,4,5) :: (List.range (n-5)).map (fun i => (i+4, i+5, i+6))

def pedigree_P3 (n : ℕ) (hn : 6 ≤ n) : Pedigree n where
  triangles    := P3triangles n
  h_n          := by omega
  h_length     := by simp [P3triangles]; omega
  h_first      := by simp [P3triangles]
  h_layers     := by
    intro i hi
    simp only [P3triangles]
    match i with
    | 0 => simp [Triple.k]
    | 1 => simp [Triple.k]
    | 2 => simp [Triple.k]
    | i+3 => simp [Triple.k]
  h_in_delta   := by
    intro i hi
    simp only [P3triangles]
    match i with
    | 0 => simp [mem_Delta_iff, Triple.i, Triple.j, Triple.k]
    | 1 => simp [mem_Delta_iff, Triple.i, Triple.j, Triple.k]
    | 2 => simp [mem_Delta_iff, Triple.i, Triple.j, Triple.k]
    | i+3 => simp [mem_Delta_iff, Triple.i, Triple.j, Triple.k]
  h_distinct   := by
    intro i j hi hj hipos hjpos hne
    simp only [P3triangles]
    match i, j with
    | 1, 2 => simp [Triple.i, Triple.j]
    | 2, 1 => simp [Triple.i, Triple.j]
    | 1, j+3 => simp [Triple.i, Triple.j]
    | j+3, 1 => simp [Triple.i, Triple.j]
    | 2, j+3 => simp [Triple.i, Triple.j]
    | j+3, 2 => simp [Triple.i, Triple.j]
    | i+3, j+3 => simp [Triple.i, Triple.j]; omega
    | 1, 1 => omega
    | 2, 2 => omega
  h_generators := by
    intro i hpos hi
    simp only [P3triangles]
    match i with
    | 0 => omega
    | 1 =>
      exact ⟨0, by omega, by simp [generators, Triple.i, Triple.j, Triple.k]⟩
    | 2 =>
      exact ⟨1, by omega, by
        simp [generators, Triple.i, Triple.j, Triple.k]⟩
    | 3 =>
      exact ⟨2, by omega, by
        simp [generators, Triple.i, Triple.j, Triple.k]⟩
    | i+4 =>
      exact ⟨i+3, by omega, by
        simp [generators, Triple.i, Triple.j, Triple.k]⟩

lemma hypSum_P3 (n : ℕ) (hn : 6 ≤ n) (C : Triple → ℚ) :
    hypSum C (pedigree_P3 n hn) = C (1,3,4) + C (1,4,5) := by
  simp only [hypSum, pedigree_P3, P3triangles]
  have hnil : ((List.range (n-5)).map (fun i => (i + 4, i + 5, i + 6))).filter
      (fun t => !isDefault t) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
    simp [isDefault, Triple.i, Triple.j, Triple.k]
  have hfull : (P3triangles n).filter (fun t => !isDefault t) = [(1,3,4), (1,4,5)] := by
    simp [P3triangles, isDefault, Triple.i, Triple.j, Triple.k]
  change (((P3triangles n).filter (fun t => !isDefault t)).map C).sum = C (1,3,4) + C (1,4,5)
  rw [hfull]; simp

-- ============================================================
-- CLAIM 2: C(1,2,4) = 0 AND C(1,3,4) = 0
-- ============================================================

theorem claim2 (n : ℕ) (hn : 6 ≤ n) (C : Triple → ℚ)
    (hC : ∀ P : Pedigree n, hypSum C P = 0) :
    C (1,2,4) = 0 ∧ C (1,3,4) = 0 := by
  have hP2 : C (1,3,4) = 0 := by
    have := hC (pedigree_P2 n hn); rw [hypSum_P2] at this; linarith
  have h145 : C (1,4,5) = 0 := by
    have := hC (pedigree_P3 n hn); rw [hypSum_P3] at this; linarith
  have hP1 : C (1,2,4) = 0 := by
    have := hC (pedigree_P1 n hn); rw [hypSum_P1] at this; linarith
  exact ⟨hP1, hP2⟩

end MembershipProject.Core
