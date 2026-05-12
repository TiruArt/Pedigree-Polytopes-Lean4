-- Core/PedigreeDefinition.lean
-- ========================================================
-- Pedigree Polytope Formalisation
-- Paper: "A Strongly Polynomial Algorithm for Membership
--        in the Pedigree Polytope" by Tiru Arthanari
-- Sections 1-2: Definition of Pedigree, Stem Property,
--               Characteristic Vectors
-- Based on: Springer Nature Book: Pedigree Polytopes
-- ========================================================

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Attach
import Mathlib.Tactic
import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_Types
import MembershipProject.Core.N_RestrictionFull

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace MembershipProject.Core

open Nat

-- ============================================================================
-- PEDIGREE COMPACT REPRESENTATION
-- ============================================================================

structure PedigreeCompact (n : ℕ) where
  edges : List (ℕ × ℕ)
  h_n : 3 ≤ n
  h_length : edges.length = n - 3
  h_ordered : ∀ e, e ∈ edges → e.1 < e.2
  h_distinct : edges.Nodup
  h_generators_compact : ∀ i, ∀ hi : i < edges.length,
      if (edges.get ⟨i, hi⟩).2 > 3 then
        ∃ idx, ∃ hidx : idx < i,
          idx + 4 = (edges.get ⟨i, hi⟩).2 ∧
          ((edges.get ⟨idx, Nat.lt_trans hidx hi⟩).1 =
            (edges.get ⟨i, hi⟩).1 ∨
           (edges.get ⟨idx, Nat.lt_trans hidx hi⟩).2 =
            (edges.get ⟨i, hi⟩).1)
      else
        True
  h_lower_bound : ∀ i, ∀ hi : i < edges.length, 1 ≤ (edges[i]).1

-- ============================================================================
-- DELTA MEMBERSHIP LEMMA (Option B)
-- Every triple in Δ_k has i ≥ 1, because i ∈ Ico 1 k by construction.
-- ============================================================================

-- ============================================================================
-- FULL PEDIGREE REPRESENTATION
-- ============================================================================

structure Pedigree (n : ℕ) where
  triangles : List Triple
  h_n : 3 ≤ n
  h_length : triangles.length = n - 2
  h_first : triangles.head? = some (Triple.mk 1 2 3 (by omega) (by omega))
  h_layers : ∀ i, ∀ hi : i < triangles.length,
    (triangles.get ⟨i, hi⟩).k = i + 3
  h_generators : ∀ i, i > 0 → ∀ hi : i < triangles.length,
    ∃ j, ∃ hj : j < i,
      (triangles.get ⟨j, Nat.lt_trans hj hi⟩) ∈
        generators (triangles.get ⟨i, hi⟩)
  h_distinct_edges : ∀ i j,
    ∀ hi : i < triangles.length,
    ∀ hj : j < triangles.length,
    i > 0 → j > 0 → i ≠ j →
    ((triangles.get ⟨i, hi⟩).i, (triangles.get ⟨i, hi⟩).j) ≠
    ((triangles.get ⟨j, hj⟩).i, (triangles.get ⟨j, hj⟩).j)
  -- Option B: every triangle lives in its Delta layer, which forces i ≥ 1
  h_in_delta : ∀ i, ∀ hi : i < triangles.length,
    (triangles.get ⟨i, hi⟩) ∈ Delta (triangles.get ⟨i, hi⟩).k

-- ============================================================================
-- LAYER ACCESS
-- ============================================================================

def Pedigree.getAtLayer {n : ℕ} (P : Pedigree n) (k : ℕ) (h : 3 ≤ k ∧ k ≤ n) :
    Option Triple :=
  let idx := k - 3
  if h_idx : idx < P.triangles.length then
    some (P.triangles.get ⟨idx, h_idx⟩)
  else
    none

def Pedigree.getEdge {n : ℕ} (P : Pedigree n) (k : ℕ) (h : 3 ≤ k ∧ k ≤ n) :
    Option (ℕ × ℕ) :=
  (P.getAtLayer k h).map fun t => (t.i, t.j)

-- ============================================================================
-- EXTENSIONALITY LEMMAS
-- ============================================================================

protected theorem Triple.ext' {t u : Triple}
    (hi : t.i = u.i) (hj : t.j = u.j) (hk : t.k = u.k) : t = u := by
  obtain ⟨ti, tj, tk, thij, thjk⟩ := t
  obtain ⟨ui, uj, uk, uhij, uhjk⟩ := u
  simp only at hi hj hk
  subst hi; subst hj; subst hk
  have e1 : thij = uhij := proof_irrel _ _
  have e2 : thjk = uhjk := proof_irrel _ _
  subst e1; subst e2; rfl

protected theorem PedigreeCompact.ext' {n : ℕ} {P Q : PedigreeCompact n}
    (h : P.edges = Q.edges) : P = Q := by
  obtain ⟨e,  hn,  hl,  ho,  hd,  hg,  hlb⟩  := P
  obtain ⟨e', hn', hl', ho', hd', hg', hlb'⟩ := Q
  simp only at h; subst h
  have e1 : hn   = hn'   := proof_irrel _ _
  have e2 : hl   = hl'   := proof_irrel _ _
  have e3 : ho   = ho'   := proof_irrel _ _
  have e4 : hd   = hd'   := proof_irrel _ _
  have e5 : hg   = hg'   := proof_irrel _ _
  have e6 : hlb  = hlb'  := proof_irrel _ _
  subst e1; subst e2; subst e3; subst e4; subst e5; subst e6; rfl

protected theorem Pedigree.ext' {n : ℕ} {P Q : Pedigree n}
    (h : P.triangles = Q.triangles) : P = Q := by
  obtain ⟨t,  hn,  hl,  hf,  hlay,  hgen,  hdist,  hdel⟩  := P
  obtain ⟨t', hn', hl', hf', hlay', hgen', hdist', hdel'⟩ := Q
  simp only at h; subst h
  have e1 : hn    = hn'    := proof_irrel _ _
  have e2 : hl    = hl'    := proof_irrel _ _
  have e3 : hf    = hf'    := proof_irrel _ _
  have e4 : hlay  = hlay'  := proof_irrel _ _
  have e5 : hgen  = hgen'  := proof_irrel _ _
  have e6 : hdist = hdist' := proof_irrel _ _
  have e7 : hdel  = hdel'  := proof_irrel _ _
  subst e1; subst e2; subst e3; subst e4; subst e5; subst e6; subst e7; rfl

-- ============================================================================
-- CHARACTERISTIC FUNCTION
-- ============================================================================

def Pedigree.toCharFunction {n : ℕ} (P : Pedigree n) : Triple → ℕ :=
  fun t => if t ∈ P.triangles then 1 else 0

-- ============================================================================
-- BASIC THEOREMS
-- ============================================================================

theorem pedigree_is_01_vector {n : ℕ} (P : Pedigree n) (t : Triple) :
    P.toCharFunction t = 0 ∨ P.toCharFunction t = 1 := by
  unfold Pedigree.toCharFunction
  by_cases h : t ∈ P.triangles
  · simp [h]
  · simp [h]

theorem pedigree_exactly_one_per_layer {n : ℕ} (P : Pedigree n) (k : ℕ)
    (h : 3 ≤ k ∧ k ≤ n) :
    ∃! t ∈ P.triangles, t.k = k := by
  have hlen := P.h_length
  have hidx : k - 3 < P.triangles.length := by omega
  refine ⟨P.triangles.get ⟨k - 3, hidx⟩,
          ⟨List.get_mem _ _, by have := P.h_layers (k-3) hidx; omega⟩,
          ?_⟩
  intro t ⟨hmem, htk⟩
  obtain ⟨⟨i, hi⟩, rfl⟩ := List.mem_iff_get.mp hmem
  have hi_eq : i = k - 3 := by
    have := P.h_layers i hi; omega
  simp [hi_eq]

-- ============================================================================
-- VALIDITY CHECKER
-- ============================================================================

noncomputable def hasGeneratorInPrefix (triangles : List Triple) (i : ℕ)
    (h : i < triangles.length) : Prop :=
  ∃ g ∈ generators (triangles.get ⟨i, h⟩), g ∈ triangles.take i

def hasDistinctEdges (triangles : List Triple) : Bool :=
  (triangles.map fun t => (t.i, t.j)).Nodup

noncomputable def validatePedigree (triangles : List Triple) (n : ℕ) : Prop :=
  triangles.length = n - 2 ∧
  (∃ t, triangles.head? = some t ∧ t.i = 1 ∧ t.j = 2 ∧ t.k = 3) ∧
  (∀ i, ∀ hi : i < triangles.length, (triangles.get ⟨i, hi⟩).k = i + 3) ∧
  (∀ i, i > 0 → ∀ hi : i < triangles.length, hasGeneratorInPrefix triangles i hi) ∧
  (∀ i j, ∀ hi : i < triangles.length, ∀ hj : j < triangles.length, i ≠ j →
    ((triangles.get ⟨i, hi⟩).i, (triangles.get ⟨i, hi⟩).j) ≠
    ((triangles.get ⟨j, hj⟩).i, (triangles.get ⟨j, hj⟩).j))

-- ============================================================================
-- TRUNCATION — COMPACT
-- ============================================================================

def PedigreeCompact.edgesUpTo {n : ℕ} (P : PedigreeCompact n) (k : ℕ)
    (h : 3 ≤ k ∧ k ≤ n) : List (ℕ × ℕ) :=
  P.edges.take (k - 3)

def PedigreeCompact.truncate {n : ℕ} (P : PedigreeCompact n) (k : ℕ)
    (h : 3 ≤ k ∧ k ≤ n) : PedigreeCompact k :=
  { edges := P.edgesUpTo k h
  , h_n := by omega
  , h_length := by
      simp only [PedigreeCompact.edgesUpTo, List.length_take]
      have hlen := P.h_length; omega
  , h_ordered := by
      intro e he
      simp only [PedigreeCompact.edgesUpTo] at he
      exact P.h_ordered e (List.mem_of_mem_take he)
  , h_distinct := by
      simp only [PedigreeCompact.edgesUpTo]
      exact (List.take_sublist _ _).nodup P.h_distinct
  , h_generators_compact := by
      intro i hi
      simp only [PedigreeCompact.edgesUpTo] at hi ⊢
      have hi' : i < P.edges.length := by
        simp only [List.length_take] at hi; omega
      have hgeti : (P.edges.take (k - 3)).get ⟨i, hi⟩ = P.edges.get ⟨i, hi'⟩ := by
        simp [List.get_eq_getElem, List.getElem_take]
      rw [hgeti]
      have hgen := P.h_generators_compact i hi'
      by_cases hj : (P.edges.get ⟨i, hi'⟩).2 > 3
      · simp only [if_pos hj] at hgen ⊢
        obtain ⟨idx, hidx, h1, h2⟩ := hgen
        have hidx' : idx < (P.edges.take (k - 3)).length := Nat.lt_trans hidx hi
        refine ⟨idx, hidx, h1, ?_⟩
        simp only [List.get_eq_getElem, List.getElem_take] at h2 ⊢
        exact h2
      · simp only [if_neg hj]
  , h_lower_bound := by
      intro i hi
      simp only [PedigreeCompact.edgesUpTo, List.length_take] at hi
      have hi' : i < P.edges.length := by omega
      simp only [PedigreeCompact.edgesUpTo, List.getElem_take]
      exact P.h_lower_bound i hi' }

-- ============================================================================
-- TRUNCATION — FULL
-- ============================================================================

def Pedigree.truncate {n : ℕ} (P : Pedigree n) (k : ℕ) (h : 3 ≤ k ∧ k ≤ n) :
    Pedigree k :=
  { triangles := P.triangles.take (k - 2)
  , h_n := by omega
  , h_length := by
      simp only [List.length_take]
      have hlen := P.h_length; omega
  , h_first := by
      have hlen : 0 < P.triangles.length := by have := P.h_length; omega
      cases ht : P.triangles with
      | nil => simp [ht] at hlen
      | cons t ts =>
          obtain ⟨m, hm⟩ : ∃ m, k - 2 = m + 1 := ⟨k - 3, by omega⟩
          simp only [hm, List.take_succ_cons, List.head?_cons]
          have := P.h_first; rw [ht] at this; exact this
  , h_layers := by
      intro i hi
      have hi' : i < P.triangles.length := by
        simp only [List.length_take] at hi; omega
      have heq : (P.triangles.take (k - 2)).get ⟨i, hi⟩ = P.triangles.get ⟨i, hi'⟩ := by
        simp [List.get_eq_getElem, List.getElem_take]
      rw [heq]; exact P.h_layers i hi'
  , h_generators := by
      intro i hpos hi
      have hi' : i < P.triangles.length := by
        simp only [List.length_take] at hi; omega
      have hgeti : (P.triangles.take (k - 2)).get ⟨i, hi⟩ = P.triangles.get ⟨i, hi'⟩ := by
        simp [List.get_eq_getElem, List.getElem_take]
      obtain ⟨j, hjlt, hgen⟩ := P.h_generators i hpos hi'
      refine ⟨j, hjlt, ?_⟩
      have hj' : j < P.triangles.length := Nat.lt_trans hjlt hi'
      have hgetj : (P.triangles.take (k - 2)).get ⟨j, Nat.lt_trans hjlt hi⟩ =
          P.triangles.get ⟨j, hj'⟩ := by
        simp [List.get_eq_getElem, List.getElem_take]
      rw [hgeti, hgetj]; exact hgen
  , h_distinct_edges := by
      intro i j hi hj hipos hjpos hij
      have hi' : i < P.triangles.length := by
        simp only [List.length_take] at hi; omega
      have hj' : j < P.triangles.length := by
        simp only [List.length_take] at hj; omega
      have hgeti : (P.triangles.take (k - 2)).get ⟨i, hi⟩ = P.triangles.get ⟨i, hi'⟩ := by
        simp [List.get_eq_getElem, List.getElem_take]
      have hgetj : (P.triangles.take (k - 2)).get ⟨j, hj⟩ = P.triangles.get ⟨j, hj'⟩ := by
        simp [List.get_eq_getElem, List.getElem_take]
      simp only [hgeti, hgetj]
      exact P.h_distinct_edges i j hi' hj' hipos hjpos hij
  , h_in_delta := by
      intro i hi
      have hi' : i < P.triangles.length := by
        simp only [List.length_take] at hi; omega
      have heq : (P.triangles.take (k - 2)).get ⟨i, hi⟩ = P.triangles.get ⟨i, hi'⟩ := by
        simp [List.get_eq_getElem, List.getElem_take]
      -- after rw, both the element and its .k component refer to P.triangles.get ⟨i, hi'⟩
      simp only [heq]
      exact P.h_in_delta i hi' }

-- ============================================================================
-- EXTENSION
-- ============================================================================

noncomputable def hasGeneratorInPedigree {k : ℕ} (base : PedigreeCompact k)
    (t : Triple) (h : t.k = k + 1) : Prop :=
  ∃ i, ∃ hi : i < base.edges.length,
    ((base.edges.get ⟨i, hi⟩).1 = t.i ∨ (base.edges.get ⟨i, hi⟩).2 = t.i) ∧ i + 4 = t.j

def PedigreeCompact.hasEdge {n : ℕ} (P : PedigreeCompact n) (e : ℕ × ℕ) : Prop :=
  e ∈ P.edges

structure PedigreeExtension (k : ℕ) where
  base : PedigreeCompact k
  new_triangle : Triple
  h_new_layer : new_triangle.k = k + 1
  new_edge : ℕ × ℕ
  h_new_edge_def : new_edge = (new_triangle.i, new_triangle.j)
  h_has_generator : hasGeneratorInPedigree base new_triangle h_new_layer
  h_not_in_base : ¬base.hasEdge new_edge

def PedigreeExtension.extend {k : ℕ} (ext : PedigreeExtension k) : PedigreeCompact (k+1) :=
  { edges := ext.base.edges ++ [ext.new_edge]
  , h_n := by have := ext.base.h_n; omega
  , h_length := by
      simp only [List.length_append, List.length_singleton]
      have hlen := ext.base.h_length
      have hn   := ext.base.h_n
      omega
  , h_ordered := by
      intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with h | rfl
      · exact ext.base.h_ordered e h
      · rw [ext.h_new_edge_def]; exact ext.new_triangle.h_ij
  , h_distinct := by
      rw [List.nodup_append]
      refine ⟨ext.base.h_distinct, List.nodup_singleton _, ?_⟩
      intro e h_in_base e' h_in_new
      simp only [List.mem_singleton] at h_in_new
      intro heq
      exact ext.h_not_in_base (h_in_new ▸ heq ▸ h_in_base)
  , h_generators_compact := by
      intro idx hidx
      have hidx_orig : idx < (ext.base.edges ++ [ext.new_edge]).length := hidx
      simp only [List.length_append, List.length_singleton] at hidx
      by_cases hidx' : idx < ext.base.edges.length
      · have hget : (ext.base.edges ++ [ext.new_edge]).get ⟨idx, hidx_orig⟩ =
            ext.base.edges.get ⟨idx, hidx'⟩ := by
          simp [List.get_eq_getElem, List.getElem_append_left hidx']
        rw [hget]
        have hbc := ext.base.h_generators_compact idx hidx'
        by_cases hj : (ext.base.edges.get ⟨idx, hidx'⟩).2 > 3
        · simp only [hj, ↓reduceIte] at hbc ⊢
          obtain ⟨w, hw, h1, h2⟩ := hbc
          refine ⟨w, hw, h1, ?_⟩
          have hw_orig : w < (ext.base.edges ++ [ext.new_edge]).length := by
            simp only [List.length_append, List.length_singleton]; omega
          have hgetw : (ext.base.edges ++ [ext.new_edge]).get ⟨w, hw_orig⟩ =
              ext.base.edges.get ⟨w, Nat.lt_trans hw hidx'⟩ := by
            simp [List.get_eq_getElem, List.getElem_append_left (Nat.lt_trans hw hidx')]
          rw [hgetw]; exact h2
        · simp only [if_neg hj]
      · have hidx_eq : idx = ext.base.edges.length := by omega
        have hget : (ext.base.edges ++ [ext.new_edge]).get ⟨idx, hidx_orig⟩ =
            ext.new_edge := by
          simp [List.get_eq_getElem, hidx_eq,
                List.getElem_append_right (le_refl _), Nat.sub_self]
        simp only [hget, ext.h_new_edge_def]
        by_cases hj : ext.new_triangle.j > 3
        · simp only [hj, ↓reduceIte]
          obtain ⟨genIdx, hgenIdx, hcond, heq_k⟩ := ext.h_has_generator
          have hgenIdx_orig : genIdx < (ext.base.edges ++ [ext.new_edge]).length := by
            simp only [List.length_append, List.length_singleton]; omega
          refine ⟨genIdx, by omega, heq_k, ?_⟩
          have hgetg : (ext.base.edges ++ [ext.new_edge]).get ⟨genIdx, hgenIdx_orig⟩ =
              ext.base.edges.get ⟨genIdx, hgenIdx⟩ := by
            simp [List.get_eq_getElem, List.getElem_append_left hgenIdx]
          simp only [hgetg]; exact hcond
        · simp only [if_neg hj]
  , h_lower_bound := by
      intro i hi_bound
      by_cases hi' : i < ext.base.edges.length
      · have heq : (ext.base.edges ++ [ext.new_edge])[i]'hi_bound =
            ext.base.edges[i]'hi' := by apply List.getElem_append_left
        simp only [heq]; exact ext.base.h_lower_bound i hi'
      · have hi_eq : i = ext.base.edges.length := by
          simp only [List.length_append, List.length_singleton] at hi_bound; omega
        obtain ⟨idx, hidx, hgen, _⟩ := ext.h_has_generator
        have h_lb : 1 ≤ ext.new_triangle.i := by
          simp only [List.get_eq_getElem] at hgen
          rcases hgen with h1 | h2
          · linarith [ext.base.h_lower_bound idx hidx]
          · linarith [ext.base.h_lower_bound idx hidx,
                      ext.base.h_ordered _ (List.getElem_mem hidx)]
        have heq : (ext.base.edges ++ [ext.new_edge])[i]'hi_bound = ext.new_edge := by
          subst hi_eq; simp [List.getElem_append_right]
        have hfst : ((ext.base.edges ++ [ext.new_edge])[i]'hi_bound).1 =
            ext.new_triangle.i :=
          calc ((ext.base.edges ++ [ext.new_edge])[i]'hi_bound).1
              = ext.new_edge.1                          := congr_arg Prod.fst heq
            _ = (ext.new_triangle.i, ext.new_triangle.j).1 := by rw [ext.h_new_edge_def]
            _ = ext.new_triangle.i                     := rfl
        linarith }

def isExtensionOf {k : ℕ} (P' : PedigreeCompact (k+1)) (P : PedigreeCompact k) : Prop :=
  ∃ (ext : PedigreeExtension k), ext.base = P ∧ ext.extend = P'

theorem extension_preserves_prefix {k : ℕ} (ext : PedigreeExtension k) :
    ext.extend.edges.take (k - 3) = ext.base.edges := by
  simp only [PedigreeExtension.extend]
  rw [List.take_append_of_le_length]
  · simp [ext.base.h_length]
  · simp [ext.base.h_length]

theorem extension_truncates_to_base {k : ℕ} (ext : PedigreeExtension k) :
    ext.extend.truncate k ⟨ext.base.h_n, Nat.le_succ k⟩ = ext.base := by
  apply PedigreeCompact.ext'
  simp only [PedigreeCompact.truncate, PedigreeCompact.edgesUpTo,
             PedigreeExtension.extend]
  rw [List.take_append_of_le_length]
  · simp [ext.base.h_length]
  · simp [ext.base.h_length]

-- DecidableEq for PedigreeCompact: equality is determined entirely by the edge list.
private instance instDecidableEqPedigreeCompact {n : ℕ} :
    DecidableEq (PedigreeCompact n) := fun P Q =>
  if h : P.edges = Q.edges then isTrue  (PedigreeCompact.ext' h)
  else                           isFalse (fun heq => h (congrArg (·.edges) heq))

/-- The finite set of all PedigreeCompact (k+1) that extend a given base.
    Each extension is uniquely determined by one new edge (a, b) with
    1 ≤ a < b < k+1, a generator for (a, b) present in base, and (a,b) novel. -/
noncomputable def allExtensions {k : ℕ} (base : PedigreeCompact k) :
    Finset (PedigreeCompact (k+1)) :=
  haveI := @instDecidableEqPedigreeCompact (k + 1)
  -- Valid new edges: use List.getD so the predicate is decidable
  -- without needing a dependent index proof inside the filter lambda.
  let valid : Finset (ℕ × ℕ) :=
    ((Finset.Ico 1 (k + 1)) ×ˢ (Finset.Ico 1 (k + 1))).filter fun e =>
      e.1 < e.2 ∧
      (∃ idx ∈ Finset.range base.edges.length,
        ((base.edges.getD idx (0, 0)).1 = e.1 ∨
         (base.edges.getD idx (0, 0)).2 = e.1) ∧
        idx + 4 = e.2) ∧
      e ∉ base.edges
  -- For each valid edge, build the unique extension via PedigreeExtension.extend.
  valid.attach.image fun ⟨e, hmem⟩ => by
    have hfilt  := (Finset.mem_filter.mp hmem).2
    have hpair  := Finset.mem_product.mp (Finset.mem_filter.mp hmem).1
    have hlt    : e.1 < e.2   := hfilt.1
    have hjk    : e.2 < k + 1 := (Finset.mem_Ico.mp hpair.2).2
    have hnotin : ¬base.hasEdge e := hfilt.2.2
    -- ∃ idx ∈ Finset.range ..., P idx  desugars to  ∃ idx, idx ∈ range ... ∧ P idx
    -- so Classical.choose_spec gives the full conjunction directly.
    have hgen : ∃ idx ∈ Finset.range base.edges.length,
        ((base.edges.getD idx (0, 0)).1 = e.1 ∨
         (base.edges.getD idx (0, 0)).2 = e.1) ∧ idx + 4 = e.2 := hfilt.2.1
    let idx          := Classical.choose hgen
    have hidx_spec   := Classical.choose_spec hgen
    have hidx        : idx < base.edges.length := Finset.mem_range.mp hidx_spec.1
    have hor_d       := hidx_spec.2.1
    have heq_layer   := hidx_spec.2.2
    -- Convert getD to direct getElem access
    have hgetD : base.edges.getD idx (0, 0) = base.edges[idx]'hidx := by
      simp only [List.getD,
        show base.edges[idx]? = some (base.edges[idx]'hidx) from by simp [hidx],
        Option.getD_some]
    have hor : (base.edges[idx]'hidx).1 = e.1 ∨
               (base.edges[idx]'hidx).2 = e.1 := hgetD ▸ hor_d
    exact (PedigreeExtension.mk base (Triple.mk e.1 e.2 (k + 1) hlt hjk)
        rfl e rfl
        ⟨idx, hidx, by simp only [List.get_eq_getElem]; exact hor, heq_layer⟩
        hnotin).extend

noncomputable def numExtensions {k : ℕ} (P : PedigreeCompact k) : ℕ :=
  (allExtensions P).card

-- ============================================================================
-- CONVERSION — COMPACT → FULL
-- ============================================================================

private lemma toFull_hjk {n : ℕ} (P : PedigreeCompact n) (i : ℕ)
    (hi : i < P.edges.length) : (P.edges[i]).2 < i + 4 := by
  have hgen := P.h_generators_compact i hi
  by_cases hj : (P.edges[i]).2 > 3
  · simp only [List.get_eq_getElem, hj, ↓reduceIte] at hgen
    obtain ⟨idx, hidx, heq, _⟩ := hgen; omega
  · push_neg at hj
    have hord := P.h_ordered _ (List.getElem_mem hi); omega

private def toFull_triple {n : ℕ} (P : PedigreeCompact n) : Fin P.edges.length → Triple :=
  fun ⟨i, hi⟩ => Triple.mk (P.edges[i]).1 (P.edges[i]).2 (i + 4)
    (P.h_ordered _ (List.getElem_mem hi))
    (toFull_hjk P i hi)

@[simp] lemma toFull_triple_k {n : ℕ} (P : PedigreeCompact n) (i : ℕ)
    (hi : i < P.edges.length) : (toFull_triple P ⟨i, hi⟩).k = i + 4 := rfl

-- Helper: toFull_triple lives in its Delta layer (uses h_lower_bound)
private lemma toFull_triple_mem_delta {n : ℕ} (P : PedigreeCompact n) (i : ℕ)
    (hi : i < P.edges.length) : toFull_triple P ⟨i, hi⟩ ∈ Delta (i + 4) := by
  have hlb  := P.h_lower_bound i hi
  have hord := P.h_ordered _ (List.getElem_mem hi)
  have hjk  := toFull_hjk P i hi
  unfold Delta
  rw [dif_pos (by omega : i + 4 ≥ 3)]
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨(P.edges[i]).1, Finset.mem_Ico.mpr ⟨hlb, by omega⟩⟩,
          Finset.mem_attach _ _, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨⟨(P.edges[i]).2, Finset.mem_Ico.mpr ⟨by omega, hjk⟩⟩,
          Finset.mem_attach _ _, ?_⟩
  simp [toFull_triple]

def PedigreeCompact.toFull {n : ℕ} (P : PedigreeCompact n) : Pedigree n :=
  { triangles :=
      Triple.mk 1 2 3 (by omega) (by omega) ::
      (List.finRange P.edges.length).map (toFull_triple P)
  , h_n := P.h_n
  , h_length := by
      simp only [List.length_cons, List.length_map, List.length_finRange, P.h_length]
      have hn := P.h_n; omega
  , h_first := by simp [List.head?_cons]
  , h_layers := by
      intro i hi
      simp only [List.length_cons, List.length_map, List.length_finRange] at hi
      cases i with
      | zero => simp [List.get_eq_getElem]
      | succ i =>
          simp only [List.get_eq_getElem, List.getElem_cons_succ,
                     List.getElem_map, List.getElem_finRange,
                     toFull_triple, Fin.val_cast]
  , h_generators := by
      intro i hpos hi
      simp only [List.length_cons, List.length_map, List.length_finRange] at hi
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hi' : i' < P.edges.length := by omega
      have hi_explicit : i' + 1 < (Triple.mk 1 2 3 (by omega) (by omega) ::
              (List.finRange P.edges.length).map (toFull_triple P)).length := by
        simp only [List.length_cons, List.length_map, List.length_finRange]; omega
      have hget_succ : ((Triple.mk 1 2 3 (by omega) (by omega) ::
              (List.finRange P.edges.length).map (toFull_triple P)).get
              ⟨i' + 1, hi_explicit⟩) = toFull_triple P ⟨i', hi'⟩ := by
        simp [List.get_eq_getElem, List.getElem_cons_succ,
              List.getElem_map, List.getElem_finRange]
      rw [hget_succ]
      have hget_0 : ∀ (h0 : 0 < (Triple.mk 1 2 3 (by omega) (by omega) ::
              (List.finRange P.edges.length).map (toFull_triple P)).length),
          ((Triple.mk 1 2 3 (by omega) (by omega) ::
            (List.finRange P.edges.length).map (toFull_triple P)).get ⟨0, h0⟩) =
          Triple.mk 1 2 3 (by omega) (by omega) := fun h0 => by
        simp [List.get_eq_getElem]
      have hti : (toFull_triple P ⟨i', hi'⟩).i = (P.edges[i']).1 := rfl
      have htj : (toFull_triple P ⟨i', hi'⟩).j = (P.edges[i']).2 := rfl
      have htk : (toFull_triple P ⟨i', hi'⟩).k = i' + 4 := rfl
      have ht_not_root : ¬((toFull_triple P ⟨i', hi'⟩).i = 1 ∧
                           (toFull_triple P ⟨i', hi'⟩).j = 2 ∧
                           (toFull_triple P ⟨i', hi'⟩).k = 3) := by simp [htk]
      have hgen := P.h_generators_compact i' hi'
      simp only [List.get_eq_getElem] at hgen
      by_cases hj : (P.edges[i']).2 > 3
      · simp only [hj, ↓reduceIte] at hgen
        obtain ⟨idx, hidx, heq_k, hor⟩ := hgen
        have hidx' : idx < P.edges.length := Nat.lt_trans hidx hi'
        refine ⟨idx + 1, by omega, ?_⟩
        have hget_idx : ((Triple.mk 1 2 3 (by omega) (by omega) ::
              (List.finRange P.edges.length).map (toFull_triple P)).get
              ⟨idx + 1, Nat.lt_trans (by omega : idx + 1 < i' + 1) hi_explicit⟩) =
            toFull_triple P ⟨idx, hidx'⟩ := by
          simp [List.get_eq_getElem, List.getElem_cons_succ,
                List.getElem_map, List.getElem_finRange]
        rw [hget_idx]
        have hui : (toFull_triple P ⟨idx, hidx'⟩).i = (P.edges[idx]).1 := rfl
        have huj : (toFull_triple P ⟨idx, hidx'⟩).j = (P.edges[idx]).2 := rfl
        have huk : (toFull_triple P ⟨idx, hidx'⟩).k = idx + 4 := rfl
        have huk_tj : (toFull_triple P ⟨idx, hidx'⟩).k =
                      (toFull_triple P ⟨i', hi'⟩).j := by rw [huk, htj]; exact heq_k
        have htij : (toFull_triple P ⟨i', hi'⟩).i < (toFull_triple P ⟨i', hi'⟩).j :=
          (toFull_triple P ⟨i', hi'⟩).h_ij
        unfold generators
        simp only [if_neg ht_not_root,
                   show (toFull_triple P ⟨i', hi'⟩).j > 3 from htj ▸ hj, ↓reduceIte]
        rcases hor with h_left | h_right
        · have hui_ti : (toFull_triple P ⟨idx, hidx'⟩).i =
                        (toFull_triple P ⟨i', hi'⟩).i := by rw [hui, hti]; exact h_left
          have h_lb : (toFull_triple P ⟨i', hi'⟩).i <
                      (toFull_triple P ⟨idx, hidx'⟩).j := by
            rw [← hui_ti, hui, huj]; exact P.h_ordered _ (List.getElem_mem hidx')
          have h_ub : (toFull_triple P ⟨idx, hidx'⟩).j <
                      (toFull_triple P ⟨i', hi'⟩).j := by
            rw [← huk_tj]; exact (toFull_triple P ⟨idx, hidx'⟩).h_jk
          apply Finset.mem_union_right
          simp only [Finset.mem_biUnion]
          refine ⟨⟨(toFull_triple P ⟨idx, hidx'⟩).j,
                   Finset.mem_Ico.mpr ⟨by omega, h_ub⟩⟩,
                  Finset.mem_attach _ _, ?_⟩
          rw [dif_pos htij]
          simp only [Option.toFinset_some, Finset.mem_singleton, toFull_triple]
          apply Triple.ext' <;> [exact h_left; rfl; exact heq_k]
        · have huj_ti : (toFull_triple P ⟨idx, hidx'⟩).j =
                        (toFull_triple P ⟨i', hi'⟩).i := by rw [huj, hti]; exact h_right
          have h_ub : (toFull_triple P ⟨idx, hidx'⟩).i <
                      (toFull_triple P ⟨i', hi'⟩).i := by
            rw [← huj_ti]; exact (toFull_triple P ⟨idx, hidx'⟩).h_ij
          have h_lb : 1 ≤ (toFull_triple P ⟨idx, hidx'⟩).i := by
            simp only [toFull_triple]; exact P.h_lower_bound idx hidx'
          apply Finset.mem_union_left
          simp only [Finset.mem_biUnion]
          refine ⟨⟨(toFull_triple P ⟨idx, hidx'⟩).i,
                   Finset.mem_Ico.mpr ⟨h_lb, h_ub⟩⟩,
                  Finset.mem_attach _ _, ?_⟩
          rw [dif_pos htij]
          simp only [Option.toFinset_some, Finset.mem_singleton, toFull_triple]
          apply Triple.ext' <;> [rfl; exact h_right; exact heq_k]
      · push_neg at hj
        refine ⟨0, by omega, ?_⟩
        rw [hget_0 (by omega)]
        unfold generators
        simp only [if_neg ht_not_root,
                   show ¬(toFull_triple P ⟨i', hi'⟩).j > 3 from by rw [htj]; omega,
                   ↓reduceIte]
        exact Finset.mem_singleton_self _
  , h_distinct_edges := by
      intro i j hi hj hipos hjpos hij
      simp only [List.length_cons, List.length_map, List.length_finRange] at hi hj
      simp only [List.get_eq_getElem]
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hi' : i' < P.edges.length := by omega
      have hj' : j' < P.edges.length := by omega
      have hij' : i' ≠ j' := fun h => hij (congrArg Nat.succ h)
      simp only [List.getElem_cons_succ, List.getElem_map,
                 List.getElem_finRange, toFull_triple]
      intro h_eq
      -- List.getElem_finRange leaves ↑(finRange.get ⟨i',_⟩) unreduced;
      -- List.get_finRange normalises it to i' so congr_arg can fire cleanly.
      simp only [List.get_finRange] at h_eq
      have heq : P.edges[i'] = P.edges[j'] :=
        Prod.ext (congr_arg Prod.fst h_eq) (congr_arg Prod.snd h_eq)
      exact hij' (P.h_distinct.getElem_inj_iff.mp heq)
  , h_in_delta := by
      intro idx hi
      simp only [List.length_cons, List.length_map, List.length_finRange] at hi
      cases idx with
      | zero =>
          simp only [List.get_eq_getElem, List.getElem_cons_zero]
          -- root {1,2,3} ∈ Delta 3
          rw [Delta, dif_pos (by omega : 3 ≥ 3)]
          apply Finset.mem_biUnion.mpr
          refine ⟨⟨1, Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩⟩,
                  Finset.mem_attach _ _, ?_⟩
          apply Finset.mem_image.mpr
          refine ⟨⟨2, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩,
                  Finset.mem_attach _ _, ?_⟩
          exact Triple.ext' rfl rfl rfl
      | succ i =>
          have hi' : i < P.edges.length := by omega
          simp only [List.get_eq_getElem, List.getElem_cons_succ,
                     List.getElem_map, List.getElem_finRange, toFull_triple_k]
          exact toFull_triple_mem_delta P i hi' }

-- ============================================================================
-- CONVERSION — FULL → COMPACT
-- ============================================================================

def Pedigree.toCompact {n : ℕ} (P : Pedigree n) : PedigreeCompact n :=
  { edges := P.triangles.tail.map fun t => (t.i, t.j)
  , h_n := P.h_n
  , h_length := by
      simp only [List.length_map, List.length_tail]
      have hlen := P.h_length; have hn := P.h_n; omega
  , h_ordered := by
      intro e he
      simp only [List.mem_map] at he
      obtain ⟨t, _, ht⟩ := he
      rw [← ht]; exact t.h_ij
  , h_distinct := by
      -- Nodup via Pairwise: distinct (i,j) pairs follow from h_distinct_edges
      unfold List.Nodup
      rw [List.pairwise_map, List.pairwise_iff_getElem]
      intro i j hi hj hij heq
      -- translate tail indices to triangles indices
      have hi' : i + 1 < P.triangles.length := by
        simp [List.length_tail] at hi; omega
      have hj' : j + 1 < P.triangles.length := by
        simp [List.length_tail] at hj; omega
      have hti : P.triangles.tail[i]'(by simpa [List.length_tail] using hi) =
          P.triangles.get ⟨i + 1, hi'⟩ := by
        simp [List.get_eq_getElem, List.getElem_tail]
      have htj : P.triangles.tail[j]'(by simpa [List.length_tail] using hj) =
          P.triangles.get ⟨j + 1, hj'⟩ := by
        simp [List.get_eq_getElem, List.getElem_tail]
      rw [hti, htj] at heq
      exact P.h_distinct_edges (i+1) (j+1) hi' hj' (by omega) (by omega) (by omega)
        (Prod.ext (congr_arg Prod.fst heq) (congr_arg Prod.snd heq))
  , h_generators_compact := by
      intro idx hidx
      have hidx_orig : idx < (P.triangles.tail.map (fun t => (t.i, t.j))).length := hidx
      simp only [List.length_map, List.length_tail] at hidx
      have hidx' : idx + 1 < P.triangles.length := by omega
      have hget : (P.triangles.tail.map (fun t => (t.i, t.j))).get ⟨idx, hidx_orig⟩ =
          ((P.triangles.get ⟨idx + 1, hidx'⟩).i,
           (P.triangles.get ⟨idx + 1, hidx'⟩).j) := by
        simp [List.get_eq_getElem, List.getElem_map, List.getElem_tail]
      rw [hget]
      set t := P.triangles.get ⟨idx + 1, hidx'⟩ with ht_def
      have htk   : t.k = idx + 4 := P.h_layers (idx + 1) hidx'
      have ht_nr : ¬(t.i = 1 ∧ t.j = 2 ∧ t.k = 3) := fun ⟨_, _, hk⟩ => by omega
      by_cases hj : t.j > 3
      · simp only [hj, ↓reduceIte]
        obtain ⟨j_pos, hj_lt, hgen⟩ := P.h_generators (idx + 1) (by omega) hidx'
        have hj_pos' : j_pos < P.triangles.length := Nat.lt_trans hj_lt hidx'
        set g := P.triangles.get ⟨j_pos, hj_pos'⟩
        have hgk  : g.k = t.j  := mem_generators_layer ht_nr hj hgen
        have hgk2 : g.k = j_pos + 3 := P.h_layers j_pos hj_pos'
        have hpos : j_pos > 0    := by omega
        have hwit_k  : (j_pos - 1) + 4 = t.j := by omega
        have hwit_lt : j_pos - 1 < idx       := by omega
        have hget_w : (P.triangles.tail.map (fun t => (t.i, t.j))).get
            ⟨j_pos - 1, Nat.lt_trans hwit_lt hidx_orig⟩ = (g.i, g.j) := by
          simp only [List.get_eq_getElem, List.getElem_map, List.getElem_tail,
                     show j_pos - 1 + 1 = j_pos from by omega]
          rfl
        refine ⟨j_pos - 1, hwit_lt, hwit_k, ?_⟩
        rw [show (P.triangles.tail.map (fun t => (t.i, t.j))).get
              ⟨j_pos - 1, Nat.lt_trans hwit_lt hidx_orig⟩ = (g.i, g.j) from hget_w]
        exact mem_generators_common_edge ht_nr hj hgen
      · simp only [if_neg hj]
  , h_lower_bound := by
      -- Option B: every triangle lives in Delta (its layer), which forces i ≥ 1
      intro i hi
      simp only [List.length_map, List.length_tail] at hi
      have hi' : i + 1 < P.triangles.length := by omega
      simp only [List.getElem_map]
      have htail : P.triangles.tail[i]'(by simp [List.length_tail]; omega) =
          P.triangles.get ⟨i + 1, hi'⟩ := by
        simp [List.get_eq_getElem, List.getElem_tail]
      simp only [htail]
      exact mem_delta_i_pos (P.h_in_delta (i + 1) hi') }

-- ============================================================================
-- THE BIJECTION BETWEEN Pedigree AND PedigreeCompact
-- ============================================================================

/-- Round trip: toFull then toCompact recovers the original PedigreeCompact. -/
theorem pedigree_full_equiv {n : ℕ} (P : PedigreeCompact n) :
    P.toFull.toCompact = P := by
  apply PedigreeCompact.ext'
  simp only [Pedigree.toCompact, PedigreeCompact.toFull, List.tail_cons, List.map_map]
  apply List.ext_getElem
  · simp [List.length_map, List.length_finRange]
  · intro i hi1 _
    simp only [List.getElem_map, List.getElem_finRange, toFull_triple]
    exact Prod.eta _

/-- Round trip: toCompact then toFull recovers the original Pedigree. -/
theorem pedigree_compact_equiv {n : ℕ} (P : Pedigree n) :
    P.toCompact.toFull = P := by
  apply Pedigree.ext'
  have hne : P.triangles ≠ [] := by
    have hlen := P.h_length; have hn := P.h_n
    intro h; simp [h] at hlen; omega
  obtain ⟨hd, tl, htl⟩ : ∃ hd tl, P.triangles = hd :: tl :=
    List.exists_cons_of_ne_nil hne
  have hroot : hd = Triple.mk 1 2 3 (by omega) (by omega) := by
    have hf := P.h_first; rw [htl] at hf
    simp only [List.head?_cons, Option.some.injEq] at hf
    exact Triple.ext' (by simp [hf]) (by simp [hf]) (by simp [hf])
  subst hroot
  apply List.ext_getElem
  · have hlen := P.h_length; have hn := P.h_n; rw [htl] at hlen
    simp only [PedigreeCompact.toFull, Pedigree.toCompact, List.length_cons,
               List.length_map, List.length_finRange, List.length_tail,
               List.tail_cons, htl]
  · intro i hi1 hi2
    cases i with
    | zero =>
        simp only [PedigreeCompact.toFull, Pedigree.toCompact, List.tail_cons,
                   htl, List.getElem_cons_zero]
    | succ i =>
        simp only [PedigreeCompact.toFull, List.getElem_cons_succ,
                   List.getElem_map, List.getElem_finRange]
        apply Triple.ext'
        · simp only [toFull_triple, Fin.val_cast, Pedigree.toCompact, List.getElem_map,
                     List.tail_cons, htl, List.getElem_cons_succ]
        · simp only [toFull_triple, Fin.val_cast, Pedigree.toCompact, List.getElem_map,
                     List.tail_cons, htl, List.getElem_cons_succ]
        · simp only [toFull_triple, Fin.val_cast]
          have hi_orig : i + 1 < P.triangles.length := by
            have hlen := P.h_length
            simp only [PedigreeCompact.toFull, Pedigree.toCompact, List.length_cons,
                       List.length_map, List.length_finRange, List.length_tail,
                       List.tail_cons] at hi1
            rw [htl] at hlen; simp only [List.length_cons] at hlen; omega
          have hlay := P.h_layers (i + 1) hi_orig
          simp only [List.get_eq_getElem] at hlay; omega

-- ============================================================================
-- LINK AT LAYER
-- ============================================================================

def getLinkAtLayer {n : ℕ} (P : Pedigree n) (l : ℕ) (h : 3 ≤ l ∧ l+1 ≤ n) :
    Option Link :=
  have hlen   := P.h_length
  have hidxl  : l - 3 < P.triangles.length := by omega
  have hidxl' : l - 2 < P.triangles.length := by omega
  let e  := P.triangles.get ⟨l - 3, hidxl⟩
  let e' := P.triangles.get ⟨l - 2, hidxl'⟩
  have hcons : e.k + 1 = e'.k := by
    simp only [e, e']
    have h1 := P.h_layers (l - 3) hidxl
    have h2 := P.h_layers (l - 2) hidxl'
    omega
  some ⟨e, e', hcons⟩

-- ============================================================================
-- MIR FEASIBILITY LEMMAS
-- ============================================================================

lemma slack_nonincreasing {n : ℕ} (F : MIRFeasible n)
    (m₁ m₂ : ℕ) (h12 : m₁ ≤ m₂) (hm2n : m₂ + 4 ≤ n + 1) (e : ℕ × ℕ) :
    F.u m₂ e ≤ F.u m₁ e := by
  induction m₂ with
  | zero =>
    have : m₁ = 0 := Nat.eq_zero_of_le_zero h12
    subst this; linarith
  | succ m ih =>
    by_cases heq : m₁ = m + 1
    · subst heq; linarith
    · have hm1m : m₁ ≤ m := Nat.lt_of_le_of_ne h12 heq |> Nat.le_of_lt_succ
      have hstep : F.u (m + 1) e ≤ F.u m e := by
        have hrec := F.u_rec m (by omega) e
        linarith [F.x_nn (m + 4) e]
      linarith [ih hm1m (by omega)]

lemma slack_ge_x {n : ℕ} (F : MIRFeasible n)
    {k : ℕ} (hk4 : 4 ≤ k) (hkn : k + 1 ≤ n) (e : ℕ × ℕ) :
    F.u (k - 3) e ≥ F.x (k + 1) e := by
  have h1 : k - 3 + 4 = k + 1 := by omega
  have h2 : k - 3 + 1 = k - 2 := by omega
  have hrec := F.u_rec (k - 3) (by omega) e
  rw [h1, h2] at hrec
  linarith [F.u_nn (k - 2) e]

-- ============================================================================
-- EVERY ACTIVE SLACK IS ONE
-- ============================================================================

lemma every_active_slack_one
    {k : ℕ}
    (combo  : ConvexCombo k)
    (indivU : ℕ → ℕ)
    (hint   : ∀ r ∈ combo.idx, indivU r = 0 ∨ indivU r = 1)
    (h_sum1 : combo.idx.sum (fun r => combo.weight r * (indivU r : ℚ)) = 1) :
    ∀ r ∈ combo.idx, indivU r = 1 := by
  intro r hr
  rcases hint r hr with h0 | h1
  · exfalso
    have hlt : combo.idx.sum (fun s => combo.weight s * (indivU s : ℚ)) <
               combo.idx.sum combo.weight := by
      apply Finset.sum_lt_sum
      · intro s hs
        rcases hint s hs with hs0 | hs1
        · simp only [hs0, Nat.cast_zero, mul_zero]; linarith [combo.pos s hs]
        · simp only [hs1, Nat.cast_one, mul_one, le_refl]
      · exact ⟨r, hr, by simp only [h0, Nat.cast_zero, mul_zero];
                         linarith [combo.pos r hr]⟩
    rw [combo.h_sum] at hlt; linarith
  · exact h1

-- ============================================================================
-- PACKABILITY COROLLARY
-- ============================================================================

section PackabilityCor

theorem packabilityCor
    {n k : ℕ} (hn : 5 ≤ n) (hk4 : 4 ≤ k) (hkn : k + 1 ≤ n)
    (F      : MIRFeasible n)
    (combo  : ConvexCombo k)
    (e'     : ℕ × ℕ)
    (hx1    : F.x (k + 1) e' = 1)
    (indivU : ℕ → ℕ)
    (hint   : ∀ r ∈ combo.idx, indivU r = 0 ∨ indivU r = 1)
    (h_agg  : combo.idx.sum (fun r => combo.weight r * (indivU r : ℚ)) =
              F.u (k - 3) e')
    (hext   : ∀ r ∈ combo.idx, indivU r = 1 →
                ∃ _ : PedigreeCompact (k + 1), True) :
    ∃ combo' : ConvexCombo (k + 1),
        combo'.idx = combo.idx ∧
        ∀ r ∈ combo.idx, combo'.weight r = combo.weight r := by
  have hu_ge1 : F.u (k - 3) e' ≥ 1 := by
    have hxge := slack_ge_x F hk4 hkn e'
    rw [hx1] at *; exact_mod_cast hxge
  have hu_le1 : F.u (k - 3) e' ≤ 1 :=
    calc F.u (k - 3) e'
        ≤ F.u 0 e' := slack_nonincreasing F 0 (k - 3) (Nat.zero_le _) (by omega) e'
      _ ≤ 1        := F.u0_le1 e'
  have hsum1 : combo.idx.sum (fun r => combo.weight r * (indivU r : ℚ)) = 1 := by
    have : (F.u (k - 3) e' : ℚ) = 1 := by exact_mod_cast le_antisymm hu_le1 hu_ge1
    linarith [h_agg]
  have h_all1 := every_active_slack_one combo indivU hint hsum1
  have _ : ∀ r ∈ combo.idx, ∃ _ : PedigreeCompact (k + 1), True :=
    fun r hr => hext r hr (h_all1 r hr)
  exact ⟨⟨combo.idx, combo.weight, combo.h_nonneg, combo.h_sum, combo.pos⟩,
         rfl, fun _ _ => rfl⟩

end PackabilityCor

-- ============================================================================
-- EXAMPLES
-- ============================================================================

/-- Fan pedigree P₅: {1,2,3}, {1,3,4}, {1,4,5} -/
def examplePedigree5 : Pedigree 5 where
  triangles := [
    Triple.mk 1 2 3 (by omega) (by omega),
    Triple.mk 1 3 4 (by omega) (by omega),
    Triple.mk 1 4 5 (by omega) (by omega)
  ]
  h_n      := by omega
  h_length := by rfl
  h_first  := by rfl
  h_layers := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> rfl
  h_generators := by
    intro i hpos hi
    simp only [List.length_cons, List.length_nil] at hi
    -- hpos : i > 0 and hi : i < 3, so exactly i = 1 or i = 2
    have hcases : i = 1 ∨ i = 2 := by omega
    rcases hcases with rfl | rfl
    · refine ⟨0, by omega, ?_⟩
      -- reduce .get ⟨n, hi⟩ to a concrete element so decide can fire
      simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ]
      decide
    · refine ⟨1, by omega, ?_⟩
      simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ]
      decide
  h_distinct_edges := by
    intro i j hi hj hipos hjpos hij
    simp only [List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;> simp_all
  h_in_delta := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hcases with rfl | rfl | rfl <;>
    simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ] <;>
    decide

/-- Compact pedigree for n=6: edges (1,3),(3,4),(1,4) -/
def examplePedigreeCompact6 : PedigreeCompact 6 where
  edges := [(1, 3), (3, 4), (1, 4)]
  h_n      := by omega
  h_length := by rfl
  h_ordered := by decide
  h_distinct := by decide
  h_generators_compact := by native_decide
  h_lower_bound := by decide

def examplePedigree6Full : Pedigree 6 := examplePedigreeCompact6.toFull

example : examplePedigree6Full.triangles.length = 4 := by
  simp [examplePedigree6Full, PedigreeCompact.toFull, examplePedigreeCompact6]

end MembershipProject.Core
