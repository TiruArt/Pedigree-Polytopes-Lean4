-- File No. 4-3 - N_PedigreeGraph.lean
--
-- Graph-theoretic formulation of Pedigrees.
--
-- The directed graph G_n:
--   Vertices: Nodes = { (i,j,k) | (i,j,k) ∈ Delta k, 3 ≤ k ≤ n }
--   Edges:    u → v iff u.triple ∈ generators v.triple
--
-- A Pedigree = a path [t₃, t₄, ..., tₙ] in G_n where:
--   t₃ = (1,2,3), tₖ is at layer k, consecutive nodes are edges.
--
-- Reference: Arthanari, T.S. arXiv:2507.09069v1 [math.CO].

import MembershipProject.Core.N_PedigreeDefinition

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MembershipProject.Core

open Nat

-- ============================================================
-- NODE: a triple together with its validity proof
-- ============================================================

/-- A Node in G_n: a valid triple t with 3 ≤ t.k ≤ n. -/
structure Node (n : ℕ) where
  triple : Triple
  valid  : triple ∈ Delta triple.k
  hk_lo  : 3 ≤ triple.k
  hk_hi  : triple.k ≤ n

instance {n : ℕ} : DecidableEq (Node n) :=
  fun a b => if h : a.triple = b.triple
    then isTrue  (by cases a; cases b; simp_all)
    else isFalse (fun h' => h (congrArg Node.triple h'))

/-- Inject a pedigree triple at position i into a Node. -/
def mkNode {n : ℕ} (P : Pedigree n) (i : ℕ) (hi : i < P.triangles.length) : Node n where
  triple := P.triangles.get ⟨i, hi⟩
  valid  := P.h_in_delta i hi
  hk_lo  := by have := P.h_layers i hi; simp [Triple.k] at this ⊢; omega
  hk_hi  := by
    have := P.h_layers i hi
    have hn := P.h_n
    simp [Triple.k] at this ⊢
    rw [P.h_length] at hi; omega

-- ============================================================
-- EDGE IN G_n
-- ============================================================

/-- u → v is an edge: u.triple generates v.triple. -/
def isEdge {n : ℕ} (u v : Node n) : Prop :=
  u.triple ∈ generators v.triple

instance {n : ℕ} (u v : Node n) : Decidable (isEdge u v) :=
  Finset.decidableMem u.triple (generators v.triple)

-- ============================================================
-- PEDIGREE PATH IN G_n
-- ============================================================

/-- A pedigree as a path in G_n.
    Nodes [t₃, t₄, ..., tₙ]: base + layers + consecutive edges. -/
structure PedigreePath (n : ℕ) where
  nodes    : List (Node n)
  h_len    : nodes.length = n - 2
  h_base   : ∃ h : 0 < nodes.length,
               (nodes.get ⟨0, h⟩).triple = (1, 2, 3)
  h_layers : ∀ i, ∀ hi : i < nodes.length,
               (nodes.get ⟨i, hi⟩).triple.k = i + 3
  h_edges  : ∀ i, ∀ hi : i + 1 < nodes.length,
               isEdge (nodes.get ⟨i, Nat.lt_of_succ_lt hi⟩)
                      (nodes.get ⟨i + 1, hi⟩)

-- ============================================================
-- DIRECTION 1: Pedigree n → PedigreePath n
-- ============================================================

/-- Wrap each triangle of P into a Node. -/
noncomputable def Pedigree.toNodeList {n : ℕ} (P : Pedigree n) : List (Node n) :=
  (List.range P.triangles.length).map fun i =>
    mkNode P i (List.mem_range.mp (List.get_mem _ _) |>.2)

-- Actually simpler: use List.mapFinRange
noncomputable def Pedigree.toNodes {n : ℕ} (P : Pedigree n) : List (Node n) :=
  List.ofFn (fun i : Fin (n - 2) =>
    mkNode P i.val (P.h_length ▸ i.isLt))

/-- Convert Pedigree to PedigreePath. -/
noncomputable def Pedigree.toPedigreePath {n : ℕ} (P : Pedigree n) : PedigreePath n where
  nodes    := P.toNodes
  h_len    := by simp [Pedigree.toNodes]
  h_base   := by
    have hn2 : 0 < n - 2 := by have := P.h_n; omega
    refine ⟨by simp [Pedigree.toNodes, hn2], ?_⟩
    simp only [Pedigree.toNodes, List.get_ofFn, mkNode]
    have hf := P.h_first
    cases htl : P.triangles with
    | nil => simp [htl] at hf
    | cons h t =>
      simp only [htl, List.head?_cons, Option.some.injEq] at hf
      have h0 : P.triangles.get ⟨0, by rw [P.h_length]; omega⟩ = h := by
        simp [htl, List.get_cons_zero]
      simp [h0, hf, Triple.i, Triple.j, Triple.k]
  h_layers := by
    intro i hi
    simp only [Pedigree.toNodes, List.get_ofFn, mkNode]
    exact P.h_layers i (P.h_length ▸ by simp at hi; exact hi)
  h_edges  := by
    intro i hi
    simp only [isEdge, Pedigree.toNodes, List.get_ofFn, mkNode]
    have hi'  : i < P.triangles.length := by
      simp [Pedigree.toNodes] at hi; rw [P.h_length]; omega
    have hi1' : i + 1 < P.triangles.length := by
      simp [Pedigree.toNodes] at hi; rw [P.h_length]; omega
    obtain ⟨j, hjlt, hgen⟩ := P.h_generators (i+1) (by omega) hi1'
    exact generators_mono j (i+1) hjlt hgen |>.elim
      (fun h => h) (fun h => absurd hjlt (not_lt.mpr (le_of_eq h)))

-- ============================================================
-- KEY LEMMA: Each edge used at most once (Tiru's observation)
-- ============================================================

/-- In a PedigreePath, the triple.j value at position p uniquely
    determines p. Equivalently: no edge (a,b) can appear as an
    insertion pair at two different positions in the path.

    Proof: the generator of node at position p lies at layer
      - triple.j     (if triple.j > 3)
      - 3            (if triple.j ≤ 3)
    By h_layers this generator is at position p-1 with layer p+2.
    So triple.j = p+2 (if j > 3) or p = 1 (if j ≤ 3).
    Position is uniquely determined by triple.j. -/
lemma triple_j_determines_position {n : ℕ} (pp : PedigreePath n)
    (p : ℕ) (hp : p < pp.nodes.length) (hpos : 0 < p) :
    if (pp.nodes.get ⟨p, hp⟩).triple.j > 3
    then (pp.nodes.get ⟨p, hp⟩).triple.j = p + 2
    else p = 1 := by
  have hedge := pp.h_edges (p-1) (by omega)
  simp only [isEdge] at hedge
  have hnebase : (pp.nodes.get ⟨p, hp⟩).triple ≠ (1, 2, 3) := fun heq => by
    have := pp.h_layers p hp; simp [Triple.k, heq] at this; omega
  simp only [generators, if_neg (by
    simp only [ne_eq]
    intro ⟨h1, h2, h3⟩
    exact hnebase (by simp [Triple.i, Triple.j, Triple.k] at h1 h2 h3 ⊢; omega))] at hedge
  have hk_prev := pp.h_layers (p-1) (by omega)
  simp only [Triple.k] at hk_prev
  split_ifs with hj
  · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Ico] at hedge
    rcases hedge with ⟨r, ⟨_, _⟩, hrfl⟩ | ⟨s, ⟨_, _⟩, hsfl⟩
    · have : (pp.nodes.get ⟨p-1, by omega⟩).triple.k =
             (pp.nodes.get ⟨p, hp⟩).triple.j := by
        simp [← hrfl, Triple.k]
      omega
    · have : (pp.nodes.get ⟨p-1, by omega⟩).triple.k =
             (pp.nodes.get ⟨p, hp⟩).triple.j := by
        simp [← hsfl, Triple.k]
      omega
  · simp only [Finset.mem_singleton] at hedge
    have : (pp.nodes.get ⟨p-1, by omega⟩).triple.k = 3 := by
      simp [hedge, Triple.k]
    omega

/-- Corollary: two nodes with the same (a,b) insertion pair must be
    at the same position. Each edge is used at most once. -/
lemma edge_used_at_most_once {n : ℕ} (pp : PedigreePath n)
    (i j : ℕ) (hi : i < pp.nodes.length) (hj : j < pp.nodes.length)
    (hpos_i : 0 < i) (hpos_j : 0 < j)
    (h_same_i : (pp.nodes.get ⟨i, hi⟩).triple.i =
                (pp.nodes.get ⟨j, hj⟩).triple.i)
    (h_same_j : (pp.nodes.get ⟨i, hi⟩).triple.j =
                (pp.nodes.get ⟨j, hj⟩).triple.j) :
    i = j := by
  have hbi := triple_j_determines_position pp i hi hpos_i
  have hbj := triple_j_determines_position pp j hj hpos_j
  have hjeq : (pp.nodes.get ⟨i, hi⟩).triple.j =
              (pp.nodes.get ⟨j, hj⟩).triple.j := h_same_j
  split_ifs at hbi hbj with hji hjj
  · rw [hjeq] at hji; rw [hji] at hjj; omega
  · rw [hjeq] at hji; rw [if_pos hji] at hbj; omega
  · rw [← hjeq] at hjj; rw [if_neg hjj] at hbi; omega
  · omega

-- ============================================================
-- DIRECTION 2: PedigreePath n → Pedigree n
-- ============================================================

/-- Convert PedigreePath to Pedigree. -/
noncomputable def PedigreePath.toPedigree {n : ℕ} (pp : PedigreePath n) : Pedigree n where
  triangles   := pp.nodes.map Node.triple
  h_n         := by
    obtain ⟨hpos, hbase⟩ := pp.h_base
    have h0 := pp.h_layers 0 hpos
    have hhi := (pp.nodes.get ⟨0, hpos⟩).hk_hi
    simp [Triple.k] at h0 ⊢; omega
  h_length    := by simp [pp.h_len]
  h_first     := by
    obtain ⟨hpos, hbase⟩ := pp.h_base
    cases hn : pp.nodes with
    | nil => exact absurd (by simp [hn]) (by omega)
    | cons h t =>
      simp only [List.map_cons, List.head?_cons]
      congr 1
      have : pp.nodes.get ⟨0, hpos⟩ = h := by
        simp [hn, List.get_cons_zero]
      rw [← this]; exact hbase
  h_layers    := by
    intro i hi
    simp only [List.length_map] at hi
    rw [List.get_map]
    exact pp.h_layers i (by simpa using hi)
  h_generators := by
    intro i hpos hi
    simp only [List.length_map] at hi
    rw [List.get_map]
    have hi' : i < pp.nodes.length := by simpa using hi
    -- The edge h_edges gives: nodes.get⟨i-1⟩ generates nodes.get⟨i⟩
    have hedge := pp.h_edges (i-1) (by omega)
    simp only [isEdge] at hedge
    rw [List.get_map] at *
    refine ⟨i - 1, by omega, ?_⟩
    convert hedge using 2 <;> congr 1 <;> omega
  h_distinct  := by
    intro i j hi hj hipos hjpos hij
    simp only [List.length_map] at hi hj
    simp only [List.get_map]
    intro ⟨heqi, heqj⟩
    -- KEY ARGUMENT (Tiru): each edge (a,b) used for insertion at most once.
    -- In G_n: the generator of node at position p is at layer = node[p].triple.j
    --   (if j > 3) or 3 (if j ≤ 3). By h_layers this is layer (p-1)+3 = p+2.
    -- So: if triple.j > 3 then p+2 = triple.j,
    --     if triple.j ≤ 3 then p+2 = 3, p = 1.
    -- In both cases position p is UNIQUELY determined by triple.j.
    -- Two nodes with the same .j value must be at the same position.
    -- Each edge used at most once: same (a,b) pair → same position
    exact hij (edge_used_at_most_once pp i j
      (by simpa using hi) (by simpa using hj)
      hipos hjpos heqi heqj)
  h_in_delta  := by
    intro i hi
    simp only [List.length_map] at hi
    rw [List.get_map]
    exact (pp.nodes.get ⟨i, by simpa using hi⟩).valid

-- ============================================================
-- EQUIVALENCE
-- ============================================================

/-- The graph-path formulation is equivalent to the list formulation. -/
theorem pedigree_graph_equiv {n : ℕ} :
    (∃ _ : Pedigree n, True) ↔ (∃ _ : PedigreePath n, True) :=
  ⟨fun ⟨P, _⟩ => ⟨P.toPedigreePath, trivial⟩,
   fun ⟨pp, _⟩ => ⟨pp.toPedigree, trivial⟩⟩

/-- Round-trip: Pedigree → Path → Pedigree preserves triangles. -/
theorem toPedigree_toNodes {n : ℕ} (P : Pedigree n) :
    P.toPedigreePath.toPedigree.triangles = P.triangles := by
  simp [PedigreePath.toPedigree, Pedigree.toPedigreePath,
        Pedigree.toNodes, List.map_ofFn, mkNode]

end MembershipProject.Core
