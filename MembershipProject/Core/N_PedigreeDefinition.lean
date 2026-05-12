-- Core/N_PedigreeDefinition.lean
--
-- Pedigree definition for the N_ system.
-- Triple = ℕ × ℕ × ℕ  (no proof fields).
-- Validity from Delta l membership.

import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_RestrictionFull

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace MembershipProject.Core

open Nat

-- ============================================================================
-- PEDIGREE
-- ============================================================================

structure Pedigree (n : ℕ) where
  triangles  : List Triple
  h_n        : 3 ≤ n
  h_length   : triangles.length = n - 2
  h_first    : triangles.head? = some (1, 2, 3)
  h_layers   : ∀ i, ∀ hi : i < triangles.length,
                 (triangles.get ⟨i, hi⟩).k = i + 3
  h_generators : ∀ i, i > 0 → ∀ hi : i < triangles.length,
                   ∃ j, ∃ hj : j < i,
                     (triangles.get ⟨j, Nat.lt_trans hj hi⟩) ∈
                       generators (triangles.get ⟨i, hi⟩)
  h_distinct : ∀ i j,
                 ∀ hi : i < triangles.length,
                 ∀ hj : j < triangles.length,
                 i > 0 → j > 0 → i ≠ j →
                 ((triangles.get ⟨i, hi⟩).i, (triangles.get ⟨i, hi⟩).j) ≠
                 ((triangles.get ⟨j, hj⟩).i, (triangles.get ⟨j, hj⟩).j)
  h_in_delta : ∀ i, ∀ hi : i < triangles.length,
                 (triangles.get ⟨i, hi⟩) ∈ Delta (triangles.get ⟨i, hi⟩).k

-- ============================================================================
-- EXTENSIONALITY
-- ============================================================================

protected theorem Pedigree.ext {n : ℕ} {P Q : Pedigree n}
    (h : P.triangles = Q.triangles) : P = Q := by
  obtain ⟨t, hn, hl, hf, hlay, hgen, hdist, hdel⟩ := P
  obtain ⟨t', hn', hl', hf', hlay', hgen', hdist', hdel'⟩ := Q
  simp only at h; subst h
  congr 1 <;> apply proof_irrel

-- ============================================================================
-- LAYER ACCESS
-- ============================================================================

def Pedigree.getAtLayer {n : ℕ} (P : Pedigree n) (k : ℕ)
    (h : 3 ≤ k ∧ k ≤ n) : Option Triple :=
  let idx := k - 3
  if hidx : idx < P.triangles.length then
    some (P.triangles.get ⟨idx, hidx⟩)
  else
    none

lemma Pedigree.getAtLayer_mem_Delta {n : ℕ} (P : Pedigree n)
    (k : ℕ) (h : 3 ≤ k ∧ k ≤ n) {t : Triple}
    (hget : P.getAtLayer k h = some t) : t ∈ Delta k := by
  simp only [Pedigree.getAtLayer] at hget
  split_ifs at hget with hidx
  · simp only [Option.some.injEq] at hget; subst hget
    have hlay := P.h_layers (k - 3) hidx
    have hk3 : (k - 3) + 3 = k := by omega
    -- hlay : (P.triangles.get ⟨k-3, hidx⟩).k = k-3+3
    -- need: t ∈ Delta k where t = P.triangles.get ⟨k-3, hidx⟩
    have hdel := P.h_in_delta (k - 3) hidx
    -- hdel : t ∈ Delta t.k
    -- hlay says t.k = k-3+3 = k
    -- hlay : t.k = k-3+3, hk3 : k-3+3 = k, hdel : t ∈ Delta t.k
    -- rewrite hdel using hlay then hk3
    -- hdel : t ∈ Delta t.k,  goal : t ∈ Delta k
    -- hlay : t.k = k-3+3 = k (after hk3)
    have htk : (P.triangles.get ⟨k - 3, hidx⟩).k = k := by omega
    rwa [htk] at hdel

-- ============================================================================
-- UNIQUE TRIANGLE PER LAYER
-- ============================================================================

lemma Pedigree.unique_at_layer {n : ℕ} (P : Pedigree n)
    (k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) :
    ∃! t ∈ P.triangles, t.k = k := by
  have hidx : k - 3 < P.triangles.length := by rw [P.h_length]; omega
  refine ⟨P.triangles.get ⟨k - 3, hidx⟩,
          ⟨List.get_mem P.triangles ⟨k - 3, hidx⟩, ?_⟩, ?_⟩
  · have := P.h_layers (k - 3) hidx
    simp [Triple.k] at this ⊢; omega
  · intro t ⟨hmem, htk⟩
    obtain ⟨⟨i, hi⟩, rfl⟩ := List.mem_iff_get.mp hmem
    have hi_eq : i = k - 3 := by
      have := P.h_layers i hi
      simp [Triple.k] at htk this; omega
    simp [hi_eq]

-- ============================================================================
-- TRUNCATION
-- ============================================================================

def Pedigree.truncate {n : ℕ} (P : Pedigree n)
    (k : ℕ) (h : 3 ≤ k ∧ k ≤ n) : Pedigree k where
  triangles := P.triangles.take (k - 2)
  h_n       := h.1
  h_length  := by
    simp only [List.length_take]; rw [P.h_length]; omega
  h_first   := by
    have hlen : 0 < P.triangles.length := by
      have := P.h_n; rw [P.h_length]; omega
    cases htl : P.triangles with
    | nil => simp [htl] at hlen
    | cons t ts =>
      obtain ⟨m, hm⟩ : ∃ m, k - 2 = m + 1 := ⟨k - 3, by omega⟩
      simp only [hm, List.take_succ_cons, List.head?_cons]
      have hf := P.h_first; rw [htl] at hf
      simp only [List.head?_cons, Option.some.injEq] at hf
      simp [hf]
  h_layers  := by
    intro i hi
    have hi' : i < P.triangles.length := by
      simp only [List.length_take] at hi; omega
    simp [List.get_eq_getElem, List.getElem_take]
    exact P.h_layers i hi'
  h_generators := by
    intro i hpos hi
    have hi' : i < P.triangles.length := by
      simp only [List.length_take] at hi; omega
    have hgeti : (P.triangles.take (k - 2)).get ⟨i, hi⟩ =
                 P.triangles.get ⟨i, hi'⟩ := by
      simp [List.get_eq_getElem, List.getElem_take]
    obtain ⟨j, hjlt, hgen⟩ := P.h_generators i hpos hi'
    have hj' : j < P.triangles.length := Nat.lt_trans hjlt hi'
    have hgetj : (P.triangles.take (k - 2)).get ⟨j, Nat.lt_trans hjlt hi⟩ =
                 P.triangles.get ⟨j, hj'⟩ := by
      simp [List.get_eq_getElem, List.getElem_take]
    exact ⟨j, hjlt, hgeti ▸ hgetj ▸ hgen⟩
  h_distinct := by
    intro i j hi hj hipos hjpos hij
    have hi' : i < P.triangles.length := by
      simp only [List.length_take] at hi; omega
    have hj' : j < P.triangles.length := by
      simp only [List.length_take] at hj; omega
    have hgeti : (P.triangles.take (k - 2)).get ⟨i, hi⟩ =
                 P.triangles.get ⟨i, hi'⟩ := by
      simp [List.get_eq_getElem, List.getElem_take]
    have hgetj : (P.triangles.take (k - 2)).get ⟨j, hj⟩ =
                 P.triangles.get ⟨j, hj'⟩ := by
      simp [List.get_eq_getElem, List.getElem_take]
    rw [hgeti, hgetj]
    exact P.h_distinct i j hi' hj' hipos hjpos hij
  h_in_delta := by
    intro i hi
    have hi' : i < P.triangles.length := by
      simp only [List.length_take] at hi; omega
    have heq : (P.triangles.take (k - 2)).get ⟨i, hi⟩ =
               P.triangles.get ⟨i, hi'⟩ := by
      simp [List.get_eq_getElem, List.getElem_take]
    simp only [heq]; exact P.h_in_delta i hi'

-- ============================================================================
-- EXTENSION
-- ============================================================================

-- Helper: convert length bound
private lemma append_length_lt {α} (l : List α) (a : α) (i : ℕ)
    (hi : i < l.length + 1) : i < (l ++ [a]).length := by
  simp [hi]

def Pedigree.extend {n : ℕ} (P : Pedigree n) (e : Triple)
    (he   : e ∈ Delta (n + 1))
    (hgen : ∃ i, ∃ hi : i < P.triangles.length,
              P.triangles.get ⟨i, hi⟩ ∈ generators e)
    (hne  : ∀ i, ∀ hi : i < P.triangles.length,
              (P.triangles.get ⟨i, hi⟩).i ≠ e.i ∨
              (P.triangles.get ⟨i, hi⟩).j ≠ e.j) :
    Pedigree (n + 1) where
  triangles := P.triangles ++ [e]
  h_n       := by have := P.h_n; omega
  h_length  := by
    simp only [List.length_append, List.length_singleton, P.h_length]
    have hn := P.h_n; omega
  h_first   := by
    have hne' : P.triangles ≠ [] := by
      have hplen := P.h_length
      have hn := P.h_n
      intro h
      simp only [h, List.length_nil] at hplen
      omega
    cases htl : P.triangles with
    | nil => exact absurd htl hne'
    | cons t ts =>
      simp only [List.cons_append, List.head?_cons]
      have := P.h_first; rw [htl] at this
      simp only [List.head?_cons] at this; exact this
  h_layers  := by
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases h : i < P.triangles.length
    · have heq : (P.triangles ++ [e]).get ⟨i, append_length_lt _ _ _ (by omega)⟩ =
                 P.triangles.get ⟨i, h⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left h]
      simp only [heq]; exact P.h_layers i h
    · have hieq : i = P.triangles.length := by omega
      have hget : (P.triangles ++ [e]).get ⟨i, by simp; omega⟩ = e := by
        simp [List.get_eq_getElem, hieq,
              List.getElem_append_right (le_refl _), Nat.sub_self]
      simp only [hget]
      have hek := mem_Delta_k he
      have hplen := P.h_length
      have hn := P.h_n
      simp only [Triple.k] at hek ⊢
      omega
  h_generators := by
    intro i hpos hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases h : i < P.triangles.length
    · have hgeti : (P.triangles ++ [e]).get ⟨i, by simp; omega⟩ =
                   P.triangles.get ⟨i, h⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left h]
      rw [hgeti]
      obtain ⟨j, hjlt, hgenj⟩ := P.h_generators i hpos h
      have hj_app : j < (P.triangles ++ [e]).length := by simp; omega
      refine ⟨j, hjlt, ?_⟩
      have hgetj : (P.triangles ++ [e]).get ⟨j, hj_app⟩ =
                   P.triangles.get ⟨j, Nat.lt_trans hjlt h⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left (Nat.lt_trans hjlt h)]
      rw [hgetj]; exact hgenj
    · have hieq : i = P.triangles.length := by omega
      have hgeti : (P.triangles ++ [e]).get ⟨i, by simp; omega⟩ = e := by
        simp [List.get_eq_getElem, hieq,
              List.getElem_append_right (le_refl _), Nat.sub_self]
      rw [hgeti]
      obtain ⟨jg, hjg, hgenj⟩ := hgen
      have hjg_app : jg < (P.triangles ++ [e]).length := by simp; omega
      refine ⟨jg, by omega, ?_⟩
      have hgetj : (P.triangles ++ [e]).get ⟨jg, hjg_app⟩ =
                   P.triangles.get ⟨jg, hjg⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left hjg]
      rw [hgetj]; exact hgenj
  h_distinct := by
    intro i j hi hj hipos hjpos hij
    simp only [List.length_append, List.length_singleton] at hi hj
    by_cases hi' : i < P.triangles.length <;>
    by_cases hj' : j < P.triangles.length
    · -- both in P
      have hgeti : (P.triangles ++ [e]).get ⟨i, by simp; omega⟩ =
                   P.triangles.get ⟨i, hi'⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left hi']
      have hgetj : (P.triangles ++ [e]).get ⟨j, by simp; omega⟩ =
                   P.triangles.get ⟨j, hj'⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left hj']
      rw [hgeti, hgetj]
      exact P.h_distinct i j hi' hj' hipos hjpos hij
    · -- i in P, j = new edge
      have hjeq : j = P.triangles.length := by omega
      have hgeti : (P.triangles ++ [e]).get ⟨i, by simp; omega⟩ =
                   P.triangles.get ⟨i, hi'⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left hi']
      have hgetj : (P.triangles ++ [e]).get ⟨j, by simp; omega⟩ = e := by
        simp [List.get_eq_getElem, hjeq,
              List.getElem_append_right (le_refl _), Nat.sub_self]
      rw [hgeti, hgetj]
      rcases hne i hi' with h | h
      · intro heq; exact h (Prod.ext_iff.mp heq).1
      · intro heq; exact h (Prod.ext_iff.mp heq).2
    · -- i = new edge, j in P
      have hieq : i = P.triangles.length := by omega
      have hgeti : (P.triangles ++ [e]).get ⟨i, by simp; omega⟩ = e := by
        simp [List.get_eq_getElem, hieq,
              List.getElem_append_right (le_refl _), Nat.sub_self]
      have hgetj : (P.triangles ++ [e]).get ⟨j, by simp; omega⟩ =
                   P.triangles.get ⟨j, hj'⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left hj']
      rw [hgeti, hgetj]
      rcases hne j hj' with h | h
      · intro heq; exact h (Prod.ext_iff.mp heq).1.symm
      · intro heq; exact h (Prod.ext_iff.mp heq).2.symm
    · omega  -- both at length — impossible
  h_in_delta := by
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases h : i < P.triangles.length
    · have heq : (P.triangles ++ [e]).get ⟨i, by simp; omega⟩ =
                 P.triangles.get ⟨i, h⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left h]
      simp only [heq]; exact P.h_in_delta i h
    · have hieq : i = P.triangles.length := by omega
      have heq : (P.triangles ++ [e]).get ⟨i, by simp; omega⟩ = e := by
        simp [List.get_eq_getElem, hieq,
              List.getElem_append_right (le_refl _), Nat.sub_self]
      simp only [heq]
      have hlay : e.k = n + 1 := mem_Delta_k he
      -- goal: e ∈ Delta e.k; hlay: e.k = n+1; he: e ∈ Delta (n+1)
      rw [hlay]; exact he

-- ============================================================================
-- getLast? LEMMA
-- ============================================================================

lemma Pedigree.getLast_layer {n : ℕ} (P : Pedigree n) :
    ∃ t, P.triangles.getLast? = some t ∧ t.k = n := by
  have hlen : 0 < P.triangles.length := by
    have := P.h_n; rw [P.h_length]; omega
  have hidx : P.triangles.length - 1 < P.triangles.length := by omega
  have hlast : P.triangles.getLast? =
               some (P.triangles.get ⟨P.triangles.length - 1, hidx⟩) := by
    rw [List.getLast?_eq_getElem?]
    simp [List.getElem?_eq_getElem hidx, List.get_eq_getElem]
  refine ⟨P.triangles.get ⟨P.triangles.length - 1, hidx⟩, hlast, ?_⟩
  have hlay := P.h_layers (P.triangles.length - 1) hidx
  -- hlay : t.k = P.triangles.length - 1 + 3
  -- goal : t.k = n
  have hplen := P.h_length
  have hn := P.h_n
  -- t.k and n are Nat, expand .k
  show (P.triangles.get ⟨P.triangles.length - 1, hidx⟩).k = n
  simp only [Triple.k] at hlay ⊢
  omega

-- ============================================================================
-- RIGID ENTRY
-- ============================================================================
-- A rigid pedigree entry: a pedigree in P_{n+1} with a positive weight.
-- R_k ⊂ P_{k+1} by construction — the ped field carries this directly.

structure RigidEntry (n : ℕ) where
  ped    : Pedigree (n + 1)  -- rigid pedigree in P_{n+1} by construction
  weight : ℚ
  w_pos  : weight > 0

-- ============================================================================
-- CONVEX WITNESS
-- ============================================================================
-- λ ∈ Λ_k(X): X/k ∈ conv(P_k) witnessed by a convex combination of pedigrees.
-- X ∈ conv(P_k) ↔ ∃ λ ∈ Λ_k(X), such that X = ∑_r λ_r X^r, X^r ∈ P_k.

structure ConvexWitness (n k : ℕ) (X : LayeredPoint n) where
  idx    : Finset ℕ
  ped    : ℕ → Pedigree k
  weight : ℕ → ℚ
  wt_pos  : ∀ r ∈ idx, weight r > 0
  wt_zero : ∀ r ∉ idx, weight r = 0  -- support condition
  wt_sum : idx.sum weight = 1
  combo  : ∀ t : Triple, t.k ≤ k →
    idx.sum (fun r => weight r *
      if t ∈ (ped r).triangles then 1 else 0) = X t

/-- Cast a convex witness along a proof k₁ = k₂. -/
def ConvexWitness.cast {n k₁ k₂ : ℕ} {X : LayeredPoint n} (h : k₁ = k₂)
    (wit : ConvexWitness n k₁ X) : ConvexWitness n k₂ X :=
  { idx    := wit.idx
    ped    := fun i => h ▸ wit.ped i
    weight := wit.weight
    wt_pos  := wit.wt_pos
    wt_zero := wit.wt_zero
    wt_sum := wit.wt_sum
    combo  := fun t ht => by subst h; exact wit.combo t ht }

end MembershipProject.Core
