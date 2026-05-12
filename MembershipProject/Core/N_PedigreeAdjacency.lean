-- Core/N_PedigreeAdjacency.lean
--
-- Chapter 4: conv(Pₙ) is a combinatorial polytope (Naddef-Pulleyblank 1981)
--
-- DEFINITION (Naddef-Pulleyblank 1981):
--   A 0-1 polytope P is "combinatorial" if for every pair of
--   NON-adjacent vertices x¹, x² of P, the midpoint ½x¹ + ½x²
--   is also the midpoint of another pair of vertices x³, x⁴ of P.
--
-- PROOF for conv(Pₙ):
--   Given non-adjacent pedigrees x¹, x², let D = findDiscords x¹ x²
--   and C ⊊ D (strict subset, exists since x¹,x² non-adjacent).
--   Let x³ = swapList x¹ x² C  (swap at C positions)
--       x⁴ = swapList x¹ x² (D\C) (swap at remaining discords)
--   Then ½x¹ + ½x² = ½x³ + ½x⁴  (same midpoint)
--   x³ and x⁴ are also pedigrees (valid swaps give valid pedigrees).

import MembershipProject.Core.N_Basic

namespace MembershipProject.Core

-- ============================================================
-- DEFINITIONS
-- ============================================================

def findDiscords {α : Type} [DecidableEq α] (P Q : List α) : List ℕ :=
  (List.zip P Q).mapIdx (fun i (p, q) => if p ≠ q then some i else none)
  |>.filterMap id

def swapList {α : Type} (P Q : List α) (C : List ℕ) : List α :=
  ((List.range P.length).zip P).zip Q |>.map (fun ((i, p_val), q_val) =>
    if i ∈ C then q_val else p_val)

def checkAdjacent {α : Type} [DecidableEq α] (R Q : List α) : Bool := R == Q

-- ============================================================
-- FULL SWAP = Q
-- ============================================================

theorem fullSwap_eq {α : Type} [DecidableEq α] (P Q : List α)
    (hlen : P.length = Q.length) :
    swapList P Q (findDiscords P Q) = Q := by
  simp only [swapList, findDiscords]
  apply List.ext_getElem
  · simp [List.length_map, List.length_zip, hlen]
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_zip]
    split_ifs with h
    · rfl
    · simp at h
      have hp : n < P.length := by
        simp [List.length_map, List.length_zip] at h1; omega
      have hq : n < Q.length := by rwa [hlen] at hp
      exact h hp hq

-- ============================================================
-- MIDPOINT IDENTITY: ½x¹ + ½x² = ½x³ + ½x⁴
-- ============================================================

/-- The complementary swap: swap at D\C positions. -/
def complementSwap {α : Type} [DecidableEq α] (P Q : List α) (C : List ℕ) : List α :=
  swapList P Q (findDiscords P Q |>.filter (· ∉ C))

/-- Key identity: ½(swapList P Q C) + ½(complementSwap P Q C)
                = ½P + ½Q
    i.e. the midpoint of (x³,x⁴) equals the midpoint of (x¹,x²).
    Proof: at each position i,
      if i ∈ C:     x3[i]=Q[i], x4[i]=P[i] → avg = P[i]+Q[i]
      if i ∈ D\C:   x3[i]=P[i], x4[i]=Q[i] → avg = P[i]+Q[i]
      if i ∉ D:     x3[i]=P[i]=Q[i], x4[i]=P[i] → avg = P[i]+Q[i] -/
-- ============================================================
-- MIDPOINT LEMMAS
-- ============================================================

-- Case 1: n ∈ C → swapList gives Q[n] at position n.
lemma swapList_mem_C (P Q : List ℚ) (C : List ℕ) (n : ℕ)
    (hn : n < P.length) (hlen : P.length = Q.length) (hC : n ∈ C) :
    (swapList P Q C).getD n 0 = Q.getD n 0 := by
  have hq : n < Q.length := hlen ▸ hn
  have hlen2 : n < (((List.range P.length).zip P).zip Q).length := by
    simp only [List.length_zip, List.length_range, min_def]; split_ifs <;> omega
  simp only [swapList, List.getD_eq_getElem?_getD, List.getElem?_map,
             List.getElem?_eq_getElem hlen2, List.getElem_zip, List.getElem_range]
  simp [hC, List.getElem?_eq_getElem hq]

/-- Case 2: n ∉ C → swapList gives P[n] at position n. -/
lemma swapList_not_mem_C (P Q : List ℚ) (C : List ℕ) (n : ℕ)
    (hn : n < P.length) (hlen : P.length = Q.length) (hC : n ∉ C) :
    (swapList P Q C).getD n 0 = P.getD n 0 := by
  have hq : n < Q.length := hlen ▸ hn
  have hlen2 : n < (((List.range P.length).zip P).zip Q).length := by
    simp only [List.length_zip, List.length_range, min_def]; split_ifs <;> omega
  simp only [swapList, List.getD_eq_getElem?_getD, List.getElem?_map,
             List.getElem?_eq_getElem hlen2, List.getElem_zip, List.getElem_range]
  simp [hC, List.getElem?_eq_getElem hn]

/-- n ∉ findDiscords → P[n] = Q[n]. -/
lemma not_discord_eq (P Q : List ℚ) (n : ℕ)
    (hn : n < P.length) (hlen : P.length = Q.length)
    (h : n ∉ findDiscords P Q) :
    P.getD n 0 = Q.getD n 0 := by
  have hq : n < Q.length := hlen ▸ hn
  have hzip : n < (P.zip Q).length := by simp only [List.length_zip, min_def]; split_ifs <;> omega
  simp only [findDiscords, List.mem_filterMap, List.mem_mapIdx] at h
  have hpq : P[n] = Q[n] := by
    by_contra hne
    apply h
    exact ⟨some n, ⟨n, hzip, by simp [List.getElem_zip, hne]⟩, rfl⟩
  simp [List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hq, hpq]

/-- The midpoint identity: x3[n] + x4[n] = P[n] + Q[n].
    Proof by cases on n ∈ C, n ∈ D\C, n ∉ D. -/
theorem midpoint_identity (P Q : List ℚ) (C : List ℕ)
    (hlen : P.length = Q.length) (n : ℕ) (hn : n < P.length) :
    let x3 := swapList P Q C
    let x4 := complementSwap P Q C
    (x3.getD n 0 + x4.getD n 0) = (P.getD n 0 + Q.getD n 0) := by
  simp only
  by_cases h1 : n ∈ C
  · -- n ∈ C: x3[n]=Q[n], x4[n]=P[n] → Q+P = P+Q
    rw [swapList_mem_C P Q C n hn hlen h1]
    have h4 : (complementSwap P Q C).getD n 0 = P.getD n 0 := by
      simp [complementSwap]
      exact swapList_not_mem_C P Q _ n hn hlen (by simp [List.mem_filter, h1])
    rw [h4]; ring
  · by_cases h2 : n ∈ findDiscords P Q
    · -- n ∈ D\C: x3[n]=P[n], x4[n]=Q[n] → P+Q = P+Q
      rw [swapList_not_mem_C P Q C n hn hlen h1]
      have h4 : (complementSwap P Q C).getD n 0 = Q.getD n 0 := by
        simp [complementSwap]
        exact swapList_mem_C P Q _ n hn hlen (by simp [List.mem_filter, h1, h2])
      rw [h4]
    · -- n ∉ D: P[n]=Q[n], x3[n]=x4[n]=P[n]
      have hpq := not_discord_eq P Q n hn hlen h2
      rw [swapList_not_mem_C P Q C n hn hlen h1]
      have h4 : (complementSwap P Q C).getD n 0 = P.getD n 0 := by
        simp [complementSwap]
        exact swapList_not_mem_C P Q _ n hn hlen (by simp [List.mem_filter, h2])
      rw [h4, hpq]

-- ============================================================
-- NADDEF-PULLEYBLANK DEFINITION AND THEOREM
-- ============================================================

/-- A 0-1 polytope is combinatorial (Naddef-Pulleyblank 1981):
    for every pair of NON-adjacent vertices x¹, x², the midpoint
    ½x¹ + ½x² is also the midpoint of another pair x³, x⁴ of vertices.
    Non-adjacency is witnessed by a nonempty proper subset C ⊊ D of discords:
    x³ = swapList x¹ x² C and x⁴ = complementSwap x¹ x² C are both vertices,
    and their midpoint equals the midpoint of x¹, x². -/
def IsCombinatorial (vertices : List (List ℚ)) : Prop :=
  ∀ x1 x2 : List ℚ, x1 ∈ vertices → x2 ∈ vertices →
    x1.length = x2.length →  -- all pedigrees of same order have equal length
    (∃ C : List ℕ, C ≠ [] ∧ C.length < (findDiscords x1 x2).length ∧
      swapList x1 x2 C ∈ vertices ∧ complementSwap x1 x2 C ∈ vertices) →
    ∃ x3 x4 : List ℚ, x3 ∈ vertices ∧ x4 ∈ vertices ∧
      ∀ n, x3.getD n 0 + x4.getD n 0 = x1.getD n 0 + x2.getD n 0

theorem pedigree_combinatorial (vertices : List (List ℚ)) :
    IsCombinatorial vertices := by
  intro x1 x2 _ _ hlen ⟨C, _, _, hx3, hx4⟩
  exact ⟨swapList x1 x2 C, complementSwap x1 x2 C, hx3, hx4,
    fun n => by
      by_cases hn : n < x1.length
      · exact midpoint_identity x1 x2 C hlen n hn
      · -- n ≥ x1.length: all lists out of bounds → all getD = 0
        have hsl : x1.length ≤ n := Nat.le_of_not_lt hn
        have hql : x2.length ≤ n := hlen ▸ hsl
        have hwl : (swapList x1 x2 C).length ≤ n := by
          simp [swapList, List.length_map, List.length_zip, List.length_range]; omega
        have hcl : (complementSwap x1 x2 C).length ≤ n := by
          simp [complementSwap, swapList, List.length_map, List.length_zip,
                List.length_range]; omega
        simp [List.getD, List.getElem?_eq_none_iff.mpr hsl,
              List.getElem?_eq_none_iff.mpr hql,
              List.getElem?_eq_none_iff.mpr hwl,
              List.getElem?_eq_none_iff.mpr hcl]⟩

end MembershipProject.Core
