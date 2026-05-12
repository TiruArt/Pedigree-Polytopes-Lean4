import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval -- For Icc
import Mathlib.Data.Finset.Max      -- For t.max
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Fin


open Finset
open BigOperators

def isPreSolution (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  S.card = n - 2 ∧
  (∀ t ∈ S, t.card = 3) ∧
  (∀ k ∈ Icc 3 n, ∃! t ∈ S, t.max = some k)


section LPModel

variable (n : ℕ) (S : Finset (Finset ℕ))

-- 1. Candidate Set (Variables): All subsets of size 3 in {1..n}
def Candidates : Finset (Finset ℕ) :=
  (Icc 1 n).powerset.filter (fun t => t.card = 3)

-- 2. LP Decision Variable: x_t = 1 if t ∈ S, else 0
def x (t : Finset ℕ) : ℕ := if t ∈ S then 1 else 0

-- 3. Integrated LP Constraints
def isLPPreSolution : Prop :=
  -- All chosen sets must be valid candidates
  S ⊆ Candidates n ∧

  -- Constraint 1: Cardinality (Σ x_t = n - 2)
  (∑ t ∈  Candidates n, x S t) = n - 2 ∧

  -- Constraint 2: Uniqueness of Max
  -- For each k in [3, n], the sum of x_t for all t with max t = k must be 1
  ∀ k ∈ Icc 3 n, (∑ t ∈  (Candidates n).filter (fun t => t.max = some k), x S t) = 1

open Classical

attribute [local instance] Classical.propDecidable

/-- A specific solution for n=4 -/
-- S = {{1, 2, 3}, {1, 2, 4}}
def S4 : Finset (Finset ℕ) := { {1, 2, 3}, {1, 2, 4} }

-- 1. View candidates as a List of Lists to avoid Repr errors
-- This uses 'sublists', which is the correct Lean 4 name for getting power sets of lists
#eval (List.range 5).sublists.filter (fun l => l.length = 3 ∧ !l.contains 0)

/-- 2. Verify that S4 is a valid solution using native_decide -/
example : isLPPreSolution 4 S4 := by
  -- Unfold definitions so Lean can compute the results
  unfold isLPPreSolution Candidates x
  native_decide

-- This avoids all noncomputable Finset code entirely
#eval (List.range 5).sublists.filter (fun l => l.length = 3 ∧ !l.contains 0)

/-- Find all valid sets S for a given n
-- We use List here instead of Finset to keep it computable for #eval -/
def findSolutions (n : ℕ) : List (List (List ℕ)) :=
  let all_triplets := (List.range (n + 1)).sublists.filter (fun l => l.length = 3 ∧ !l.contains 0)
  -- Generate all possible combinations of size (n-2) from those triplets
  let possible_S := all_triplets.sublists.filter (fun s => s.length = n - 2)
  -- Filter based on your 'Uniqueness of Max' constraint
  possible_S.filter (fun s =>
    (List.range (n - 2)).all (fun i =>
      let k := i + 3
      (s.filter (fun t => t.max? = some k)).length = 1
    )
  )
-- Ensure there is a blank line above the #eval
#eval findSolutions 4

-- Ensure previous imports (Basic, Card, Interval, Max, BigOperators, Fin) are present

section LPModel5
variable (S : Finset (Finset ℕ))

/-- Linearised isLPSolution for n=5 -/
def isLPSolution5 : Prop :=
  isLPPreSolution 5 S ∧
  ∀ t1 ∈ Candidates 5, ∀ t2 ∈ Candidates 5,
    let k1 := t1.max.getD 0
    let k2 := t2.max.getD 0
    let base1 := t1.erase k1
    let base2 := t2.erase k2
    (k1 ≥ 4 ∧ k2 ≥ 4 ∧ k1 < k2 ∧ base1 = base2) → (x S t1 + x S t2 ≤ 1)

/-- Computable search for n=5 solutions -/
def findSolutions5 : List (List (List ℕ)) :=
  let all_triplets := (List.range 6).sublists.filter (fun l => l.length = 3 ∧ !l.contains 0)
  let possible_S := all_triplets.sublists.filter (fun s => s.length = 3)
  possible_S.filter (fun s =>
    -- 1. Uniqueness of Max Check
    (List.range 3).all (fun i => (s.filter (fun t => t.getLast? = some (i + 3))).length = 1) ∧
    -- 2. Base Uniqueness Check
    s.all (fun t1 => s.all (fun t2 =>
      let k1 := t1.getLast!
      let k2 := t2.getLast!
      (k1 ≥ 4 ∧ k2 ≥ 4 ∧ k1 < k2) → (t1.erase k1) ≠ (t2.erase k2)
    ))
  )

#eval findSolutions5




/-! ### 3. Computable Search for n=5 -/

def findDesiredSolutions5 : List (List (List ℕ)) :=
  let all_triplets := (List.range 6).sublists.filter (fun l => l.length = 3 ∧ !l.contains 0)
  let possible_S := all_triplets.sublists.filter (fun s => s.length = 3)
  possible_S.filter (fun s =>
    -- Max Uniqueness
    (List.range 3).all (fun i => (s.filter (fun t => t.getLast? = some (i + 3))).length = 1) ∧
    -- Base Uniqueness
    s.all (fun t1 => s.all (fun t2 =>
      let k1 := t1.getLast!; let k2 := t2.getLast!
      (k1 ≥ 4 ∧ k2 ≥ 4 ∧ k1 < k2) → (t1.filter (· ≠ k1)) ≠ (t2.filter (· ≠ k2))
    )) ∧
    -- Chaining
    s.all (fun t =>
      let k := t.getLast!; let pair := t.filter (· ≠ k)
      let a := pair.min?.getD 0; let b := pair.max?.getD 0
      (pair.all (· ≤ 3)) ∨ (s.any (fun tp => tp.getLast! = b ∧ tp.contains a))
    )
  )

#eval findDesiredSolutions5.length -- Should return 12
#eval findDesiredSolutions5        -- Displays the 12 chains
-- S6 = {{1, 2, 3}, {1, 2, 4},{1, 2, 5},{ 1, 2, 6} }
def S6 : Finset (Finset ℕ) := { {1, 2, 3}, {1, 2, 4}, {1, 2, 5},{ 1, 2, 6} }
-- 1. View candidates as a List of Lists to avoid Repr errors
-- This uses 'sublists', which is the correct Lean 4 name for getting power sets of lists
#eval (List.range 7).sublists.filter (fun l => l.length = 3 ∧ !l.contains 0)
example : isLPPreSolution 6 S6 := by
  -- Unfold definitions so Lean can compute the results
  unfold isLPPreSolution Candidates x
  native_decide
