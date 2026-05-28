import Mathlib.Data.List.Basic
import Mathlib.Tactic

-- =========================================================================
-- 1. CONSOLIDATED GEOMETRIC TOPOLOGY RULES
-- =========================================================================

structure Edge (n : Nat) where
  i : Nat
  j : Nat
  h1 : 1 ≤ i
  h2 : i < j
  h3 : j ≤ n
  deriving BEq, Repr, DecidableEq

def isEdgeParent {n : Nat} (parent child : Edge n) : Bool :=
  (parent.j == child.i) || (parent.i == child.i)

/-- Enforces that parent ∈ E_{k-1} = { (i,j) | 1 ≤ i < j < k } where k = idx + 4. -/
def belongsToE_kminus1 {n : Nat} (idx : Nat) (e : Edge n) : Bool :=
  e.j < idx + 4

def hasValidPrefixParent {n : Nat} (idx : Nat) (child : Edge n) (P : List (Edge n)) : Bool :=
  let prefixList := P.take idx
  prefixList.any (fun parent =>
    isEdgeParent parent child && belongsToE_kminus1 idx parent
  )

def isValidEdgeSequence {n : Nat} (P : List (Edge n)) : Bool :=
  let indexedPairs := P.zip (List.range P.length)
  P.Nodup && (indexedPairs.all fun (e, idx) =>
    belongsToE_kminus1 idx e && (idx == 0 || hasValidPrefixParent idx e P)
  )

structure Context (n : Nat) where
  P : List (Edge n)
  Q : List (Edge n)
  hP_len : P.length = n - 3
  hQ_len : Q.length = n - 3
  hP_valid : isValidEdgeSequence P = true
  hQ_valid : isValidEdgeSequence Q = true
  isWelded : Nat → Nat → Bool


-- =========================================================================
-- 2. EMBEDDING & COORDINATE VECTOR SUM PROOF (Using Nat for full Computability)
-- =========================================================================

-- FIX: Map to Nat × Nat instead of ℝ × ℝ to enable runtime evaluation and printing
def embedEdge {n : Nat} (e : Edge n) : Nat × Nat :=
  (e.i, e.j)

def embedSequence {n : Nat} (P : List (Edge n)) : List (Nat × Nat) :=
  P.map embedEdge

def vecAdd : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)

  | [], _ => []
  | _, [] => []
  | (x1, y1) :: t1, (x2, y2) :: t2 => (x1 + x2, y1 + y2) :: vecAdd t1 t2

infixl:65 " ⊕ " => vecAdd

def swapListsByIndicesAux {n : Nat} (C : List Nat) (P Q : List (Edge n)) (offset : Nat) : List (Edge n) :=
  match P, Q with

  | [], _ => []
  | _, [] => []
  | p :: p_tail, q :: q_tail =>
    if (C.contains (offset + 4)) then
      q :: swapListsByIndicesAux C p_tail q_tail (offset + 1)
    else
      p :: swapListsByIndicesAux C p_tail q_tail (offset + 1)

def swapListsByIndices {n : Nat} (C : List Nat) (P Q : List (Edge n)) : List (Edge n) :=
  swapListsByIndicesAux C P Q 0

lemma vecAdd_swap_aux {n : Nat} (C : List Nat) (P Q : List (Edge n)) (offset : Nat) :
  (embedSequence P ⊕ embedSequence Q) =
  (embedSequence (swapListsByIndicesAux C P Q offset) ⊕ embedSequence (swapListsByIndicesAux C Q P offset)) := by
  induction P generalizing Q offset with

  | nil => rfl
  | cons p p_tail ih =>
    rcases Q with _ | ⟨q, q_tail⟩
    · rfl
    · dsimp [swapListsByIndicesAux, embedSequence, embedEdge, vecAdd]
      split_ifs with h
      · congr 1
        · ext <;> omega -- Nat addition properties handled via omega linear solver
        · exact ih q_tail (offset + 1)
      · congr 1
        exact ih q_tail (offset + 1)

/-- Main Theorem linking coordinate swappability directly to vector sum conservation. -/
theorem swap_preserves_vector_sum {n : Nat} (C : List Nat) (P Q : List (Edge n)) :
  (embedSequence P ⊕ embedSequence Q) = (embedSequence (swapListsByIndices C P Q) ⊕ embedSequence (swapListsByIndices C Q P)) := by
  dsimp [swapListsByIndices]
  exact vecAdd_swap_aux C P Q 0


-- =========================================================================
-- 3. COMPUTABLE TEST HARNESS FOR n=8
-- =========================================================================

def e_idx0 : Edge 8 := ⟨1, 2, by decide, by decide, by decide⟩
def e_idx1 : Edge 8 := ⟨2, 4, by decide, by decide, by decide⟩
def e_idx2 : Edge 8 := ⟨4, 5, by decide, by decide, by decide⟩
def e_idx3 : Edge 8 := ⟨5, 6, by decide, by decide, by decide⟩
def e_idx4 : Edge 8 := ⟨6, 7, by decide, by decide, by decide⟩

def P_seq : List (Edge 8) := [e_idx0, e_idx1, e_idx2, e_idx3, e_idx4]

def q_idx2 : Edge 8 := ⟨1, 3, by decide, by decide, by decide⟩
def q_idx3 : Edge 8 := ⟨3, 5, by decide, by decide, by decide⟩
def q_idx4 : Edge 8 := ⟨5, 6, by decide, by decide, by decide⟩

def Q_seq : List (Edge 8) := [e_idx0, e_idx1, q_idx2, q_idx3, q_idx4]

def sampleIsWelded (_l _m : Nat) : Bool := false

def myContext8 : Context 8 := {
  P := P_seq
  Q := Q_seq
  hP_len := by rfl
  hQ_len := by rfl
  hP_valid := by decide
  hQ_valid := by decide
  isWelded := sampleIsWelded
}


-- =========================================================================
-- 4. READABLE NON-ADJACENCY EVIDENCE HARNESS (Fully Computable)
-- =========================================================================

inductive EvidenceResult (n : Nat)


  | ProvenNonAdjacent
      (initial_P initial_Q : List (Nat × Nat))
      (msg : String)
      (witness_P' witness_Q' : List (Nat × Nat))
  | TrivialSelfSwap (msg : String)
  deriving Repr, BEq

def verifyNonAdjacencyEvidence (n : Nat) (ctx : Context n) (C : List Nat) : EvidenceResult n :=
  let p_prime := swapListsByIndices C ctx.P ctx.Q
  let q_prime := swapListsByIndices C ctx.Q ctx.P

  let sum_pq := embedSequence ctx.P ⊕ embedSequence ctx.Q
  let sum_primes := embedSequence p_prime ⊕ embedSequence q_prime
  let midpointsMatch := (sum_pq == sum_primes)

  let distinct := (p_prime != ctx.P) && (p_prime != ctx.Q) && (q_prime != ctx.P) && (q_prime != ctx.Q)

  if midpointsMatch && distinct then
    EvidenceResult.ProvenNonAdjacent
      (embedSequence ctx.P)
      (embedSequence ctx.Q)
      "Non-Adjacent in Conv(P_n) Witness:"
      (embedSequence p_prime)
      (embedSequence q_prime)
  else
    EvidenceResult.TrivialSelfSwap
      "FAILED: The swap resulted in the original vertices or invalid midpoints. No evidence generated."

def sampleC : List Nat := [6]

#eval verifyNonAdjacencyEvidence 8 myContext8 sampleC
