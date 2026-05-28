import Mathlib.Data.List.Basic
import Mathlib.Tactic

-- =========================================================================
-- 1. BASE DEFINITIONS & CONTEXT
-- =========================================================================

structure Edge (n : Nat) where
  i : Nat
  j : Nat
  h1 : 1 ≤ i
  h2 : i < j
  h3 : j ≤ n
  deriving BEq, Repr, DecidableEq

structure Context (n : Nat) where
  P : List (Edge n)
  Q : List (Edge n)
  hP_len : P.length = n - 3
  hQ_len : Q.length = n - 3
  isWelded : Nat → Nat → Bool

inductive FlexibilityResult (n : Nat)

  | Flexible (P_prime Q_prime : List (Edge n))
  | FullyRigid
  deriving Repr

-- =========================================================================
-- 2. TRANSFORMATION AND DESCENT SELECTION ENGINE
-- =========================================================================

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

def isProperSubset (C D : List Nat) : Bool :=
  C.all (fun x => D.contains x) && D.any (fun x => !C.contains x)

def swapComponents {n : Nat} (D C : List Nat) (P Q : List (Edge n)) : List (Edge n) × List (Edge n) :=
  if !C.isEmpty && isProperSubset C D then
    (swapListsByIndices C P Q, swapListsByIndices C Q P)
  else
    (P, Q)

def findLowerWeld (q : Nat) (D_tail : List Nat) (isWelded : Nat → Nat → Bool) : Option Nat :=
  D_tail.find? (fun l => l < q && isWelded q l)

def getHigherWeldedComponents (q : Nat) (D_all : List Nat) (isWelded : Nat → Nat → Bool) : List Nat :=
  D_all.filter (fun r => r > q && isWelded q r)

/-- Core Descent Loop over the sorted list of discords. -/
def findFlexibleSearch (n : Nat) (ctx : Context n) (D_descending : List Nat) (D_global : List Nat) : FlexibilityResult n :=
  match D_descending with

  | [] => FlexibilityResult.FullyRigid
  | q :: rest =>
    if q ≤ 3 then
      findFlexibleSearch n ctx rest D_global
    else
      match findLowerWeld q rest ctx.isWelded with

      | some _ => findFlexibleSearch n ctx rest D_global
      | none =>
        let higherWelds := getHigherWeldedComponents q D_global ctx.isWelded
        let C := (q :: higherWelds).eraseDups
        let (P_prime, Q_prime) := swapComponents D_global C ctx.P ctx.Q
        FlexibilityResult.Flexible P_prime Q_prime
