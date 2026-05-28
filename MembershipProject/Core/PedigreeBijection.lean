import Mathlib.Data.List.Basic
import Mathlib.Tactic

-- =========================================================================
-- 1. BASE MATERIAL ABBREVIATIONS & PROJECTIONS
-- =========================================================================

abbrev Triple := ℕ × ℕ × ℕ

namespace Triple
abbrev i (t : Triple) : ℕ := t.1
abbrev j (t : Triple) : ℕ := t.2.1
abbrev k (t : Triple) : ℕ := t.2.2
end Triple

-- Opaque predicates to satisfy structural constraints
opaque isValidEdgeSequence {n : Nat} (P : List (Nat × Nat)) : Bool
opaque generators (t : Triple) : Finset Triple
opaque Delta {n : Nat} (k : Nat) : Finset Triple


-- =========================================================================
-- 2. CLEANLY STRUCTURING PEDIGREE CONTEXTS
-- =========================================================================

structure Pedigree (n : Nat) where
  triangles    : List Triple
  h_n          : 3 ≤ n
  h_length     : triangles.length = n - 2
  h_first      : triangles.head? = some (1, 2, 3)

  h_layers     : ∀ i, ∀ (hi : i < triangles.length),
                   (triangles.get ⟨i, hi⟩).k = i + 3

  h_generators : ∀ i, i > 0 → ∀ (hi : i < triangles.length),
                   ∃ j, ∃ (hj : j < i),
                     triangles.get ⟨j, Nat.lt_trans hj hi⟩ ∈ generators (triangles.get ⟨i, hi⟩)

  h_distinct   : ∀ i j, ∀ (hi : i < triangles.length), ∀ (hj : j < triangles.length),
                   i > 0 → j > 0 → i ≠ j →
                   ((triangles.get ⟨i, hi⟩).i, (triangles.get ⟨i, hi⟩).j) ≠
                   ((triangles.get ⟨j, hj⟩).i, (triangles.get ⟨j, hj⟩).j)

  h_in_delta   : ∀ i, ∀ (hi : i < triangles.length),
                   triangles.get ⟨i, hi⟩ ∈ Delta (n := n) (triangles.get ⟨i, hi⟩).k


-- =========================================================================
-- 3. OFFSET-CORRECTED EXTRACTION RUNTIMES
-- =========================================================================

def pedigreeToEdges (triangles : List Triple) : List (Nat × Nat) :=
  let remainingTriangles := triangles.tail
  remainingTriangles.map fun t => (t.i, t.j)

def edgesToPedigreeAux (edges : List (Nat × Nat)) (offset : Nat) : List Triple :=
  match edges with


  | [] => []
  | e :: tail => (e.1, e.2, offset) :: edgesToPedigreeAux tail (offset + 1)

def edgesToPedigree (edges : List (Nat × Nat)) : List Triple :=
  (1, 2, 3) :: edgesToPedigreeAux edges 4


-- =========================================================================
-- 4. HIGH-DENSITY ROUND-TRIP IDENTITY THEOREM
-- =========================================================================

lemma pedigreeToEdges_aux_identity (E : List (Nat × Nat)) (offset : Nat) :
  List.map (fun t => (Triple.i t, Triple.j t)) (edgesToPedigreeAux E offset) = E := by
  induction E generalizing offset with


  | nil => rfl
  | cons head tail ih =>
    dsimp [edgesToPedigreeAux]
    congr 1
    exact ih (offset + 1)

theorem pedigree_edge_inverse_identity (E : List (Nat × Nat)) :
  pedigreeToEdges (edgesToPedigree E) = E := by
  dsimp [pedigreeToEdges, edgesToPedigree]
  exact pedigreeToEdges_aux_identity E 4


-- =========================================================================
-- 5. ADVANCED SYSTEM EVALUATION WINDOW (n=5, n=6, and n=7)
-- =========================================================================

--------------------
-- CASE 1: n = 5
--------------------
def edges5 : List (Nat × Nat) := [(1, 2), (2, 4)]
def pedigree5 : List Triple := [(1, 2, 3), (1, 2, 4), (2, 4, 5)]

#eval pedigreeToEdges pedigree5
#eval edgesToPedigree edges5
#eval pedigreeToEdges (edgesToPedigree edges5)


--------------------
-- CASE 2: n = 6
--------------------
-- Sequence P: [(1, 2), (2, 4), (4, 5)]
def edges6_P : List (Nat × Nat) := [(1, 2), (2, 4), (4, 5)]
def pedigree6_P : List Triple := [(1, 2, 3), (1, 2, 4), (2, 4, 5), (4, 5, 6)]

-- Sequence Q: [(1, 2), (1, 3), (3, 5)]
def edges6_Q : List (Nat × Nat) := [(1, 2), (1, 3), (3, 5)]
def pedigree6_Q : List Triple := [(1, 2, 3), (1, 2, 4), (1, 3, 5), (3, 5, 6)]

-- Forward evaluation checking for n=6
#eval pedigreeToEdges pedigree6_P
#eval pedigreeToEdges pedigree6_Q

-- Reverse and Round-Trip evaluation checking for n=6
#eval edgesToPedigree edges6_P
#eval pedigreeToEdges (edgesToPedigree edges6_P)


--------------------
-- CASE 3: n = 7
--------------------
-- Sequence P: [(1, 2), (2, 4), (4, 5), (5, 6)]
def edges7_P : List (Nat × Nat) := [(1, 2), (2, 4), (4, 5), (5, 6)]
def pedigree7_P : List Triple := [(1, 2, 3), (1, 2, 4), (2, 4, 5), (4, 5, 6), (5, 6, 7)]

-- Sequence Q: [(1, 2), (2, 4), (2, 3), (3, 6)]
def edges7_Q : List (Nat × Nat) := [(1, 2), (2, 4), (2, 3), (3, 6)]
def pedigree7_Q : List Triple := [(1, 2, 3), (1, 2, 4), (2, 4, 5), (2, 3, 6), (3, 6, 7)]

-- Forward evaluation checking for n=7
#eval pedigreeToEdges pedigree7_P
#eval pedigreeToEdges pedigree7_Q

-- Reverse and Round-Trip evaluation checking for n=7
#eval edgesToPedigree edges7_P
#eval edgesToPedigree edges7_Q
#eval pedigreeToEdges (edgesToPedigree edges7_P)
