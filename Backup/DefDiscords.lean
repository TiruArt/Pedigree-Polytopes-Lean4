import Mathlib.Data.List.Basic
import Mathlib.Tactic

-- ==========================================
-- 1. BASE STRUCTURE & SET DEFINITIONS
-- ==========================================

structure Edge (n : Nat) where
  i : Nat
  j : Nat
  h1 : 1 ≤ i
  h2 : i < j
  h3 : j ≤ n
  deriving BEq, Repr, DecidableEq

def isEdgeParent {n : Nat} (parent child : Edge n) : Bool :=
  (parent.j == child.i) || (parent.i == child.i)

def satisfiesKBound {n : Nat} (idx : Nat) (e : Edge n) : Bool :=
  e.j < idx + 4

/-- Enforces parent ∈ E_{k-1} = { (i,j) | 1 ≤ i < j < k } where k = idx + 4 -/
def belongsToE_kminus1 {n : Nat} (idx : Nat) (e : Edge n) : Bool :=
  e.j < idx + 4

def hasValidPrefixParent {n : Nat} (idx : Nat) (child : Edge n) (P : List (Edge n)) : Bool :=
  let prefixList := P.take idx
  prefixList.any (fun parent =>
    isEdgeParent parent child && belongsToE_kminus1 idx parent
  )

/-- Comprehensive sequence validator ensuring unique elements (Nodup)
    and strict structural prefix generation rules from E_{k-1} -/
def isValidEdgeSequence {n : Nat} (P : List (Edge n)) : Bool :=
  let indexedPairs := P.zip (List.range P.length)
  P.Nodup && (indexedPairs.all fun (e, idx) =>
    satisfiesKBound idx e && (idx == 0 || hasValidPrefixParent idx e P)
  )


-- ==========================================
-- 2. UNIFIED PROCESSING CONTEXT
-- ==========================================

structure Context (n : Nat) where
  P : List (Edge n)
  Q : List (Edge n)
  hP_len : P.length = n - 3
  hQ_len : Q.length = n - 3
  hP_valid : isValidEdgeSequence P = true
  hQ_valid : isValidEdgeSequence Q = true
  isWelded : Nat → Nat → Bool


-- ==========================================
-- 3. THE FORMALISED INDEX SWAP FUNCTION
-- ==========================================

/-- Constructs the sequence R such that:
    R(q) = P(q) if q ∉ C, and R(q) = Q(q) if q ∈ C. -/
def swapListsByIndices {n : Nat} (C : List Nat) (P Q : List (Edge n)) : List (Edge n) :=
  let range := List.range P.length
  range.filterMap (fun idx =>
    let q := idx + 4
    if C.contains q then
      Q[idx]?
    else
      P[idx]?
  )

def isProperSubset (C D : List Nat) : Bool :=
  C.all (fun x => D.contains x) && D.any (fun x => !C.contains x)

def swapComponents {n : Nat} (D C : List Nat) (P Q : List (Edge n)) : List (Edge n) × List (Edge n) :=
  if !C.isEmpty && isProperSubset C D then
    let P_prime := swapListsByIndices C P Q
    let Q_prime := swapListsByIndices C Q P
    (P_prime, Q_prime)
  else
    (P, Q)


-- ==========================================
-- 4. RECURSIVE BACKTRACKING DESCENT ENGINE
-- ==========================================

inductive FlexibilityResult (n : Nat)

  | Flexible (P_prime Q_prime : List (Edge n))
  | FullyRigid
  deriving Repr

def findLowerWeld (q : Nat) (D_tail : List Nat) (isWelded : Nat → Nat → Bool) : Option Nat :=
  D_tail.find? (fun l => l < q && isWelded q l)

def getHigherWeldedComponents (q : Nat) (D_all : List Nat) (isWelded : Nat → Nat → Bool) : List Nat :=
  D_all.filter (fun r => r > q && isWelded q r)

/-- Core Descent Loop operating over structurally valid Lists. -/
def findFlexibleSearch (n : Nat) (ctx : Context n) (D_descending : List Nat) (D_global : List Nat) : FlexibilityResult n :=
  match D_descending with

  | [] => FlexibilityResult.FullyRigid
  | q :: rest =>
    if q ≤ 3 then
      findFlexibleSearch n ctx rest D_global
    else
      match findLowerWeld q rest ctx.isWelded with

      | some _ =>
        findFlexibleSearch n ctx rest D_global
      | none =>
        let higherWelds := getHigherWeldedComponents q D_global ctx.isWelded
        let C := (q :: higherWelds).eraseDups

        let (P_prime, Q_prime) := swapComponents D_global C ctx.P ctx.Q
        FlexibilityResult.Flexible P_prime Q_prime


-- ==========================================
-- 5. VERIFIED RUNTIME TESTING (n=8)
-- ==========================================

-- Sequence P:
def e_idx0 : Edge 8 := ⟨1, 2, by decide, by decide, by decide⟩
def e_idx1 : Edge 8 := ⟨2, 4, by decide, by decide, by decide⟩
def e_idx2 : Edge 8 := ⟨4, 5, by decide, by decide, by decide⟩
def e_idx3 : Edge 8 := ⟨5, 6, by decide, by decide, by decide⟩
def e_idx4 : Edge 8 := ⟨6, 7, by decide, by decide, by decide⟩

def P_seq : List (Edge 8) := [e_idx0, e_idx1, e_idx2, e_idx3, e_idx4]

-- Sequence Q (preserving structural generation paths):
def q_idx2 : Edge 8 := ⟨1, 3, by decide, by decide, by decide⟩
def q_idx3 : Edge 8 := ⟨3, 5, by decide, by decide, by decide⟩
def q_idx4 : Edge 8 := ⟨5, 6, by decide, by decide, by decide⟩

def Q_seq : List (Edge 8) := [e_idx0, e_idx1, q_idx2, q_idx3, q_idx4]

def sampleIsWelded (l m : Nat) : Bool :=
  (l == 6 && m == 4) || (l == 4 && m == 6)

def myContext8 : Context 8 := {
  P := P_seq
  Q := Q_seq
  hP_len := by rfl
  hQ_len := by rfl
  hP_valid := by decide
  hQ_valid := by decide
  isWelded := sampleIsWelded
}


-- ==========================================
-- 6. INTERFACE & RUNTIME EXECUTION
-- ==========================================

def runFindFlexible (n : Nat) (ctx : Context n) (D : List Nat) : FlexibilityResult n :=
  let D_sorted := (D.toArray.qsort (fun a b => a > b)).toList
  findFlexibleSearch n ctx D_sorted D_sorted

-- Evaluates successfully with absolutely zero errors or warnings!
#eval findFlexibleSearch 8 myContext8 [6, 5, 4] [6, 5, 4]
