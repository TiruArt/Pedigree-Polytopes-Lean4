import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

open Finset

/-- Mathematical definition of a pre-solution -/
def isPreSolution (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  S.card = n - 2 ∧
  (∀ t ∈ S, t.card = 3) ∧
  (∀ k ∈ Icc 3 n, ∃! t ∈ S, t.max = some k)

/--
  Computable checker.
  To check "all elements satisfy p", we ensure the set of elements
  NOT satisfying p is empty.
-/
def checkPreSolution (n : ℕ) (S : Finset (Finset ℕ)) : Bool :=
  let correct_count := S.card == n - 2
  let all_triplets := S.filter (λ t => t.card != 3) == ∅
  let all_maxes_covered := (Icc 3 n).filter (λ k =>
    (S.filter (λ t => t.max == some k)).card != 1
  ) == ∅
  correct_count && all_triplets && all_maxes_covered

/--
  The natural pre-solution construction.
  Uses 'Finset.image' instead of 'map' to bypass the immediate
  need for an injectivity proof, making it easier to compile.
-/
def naturalPreSolution (n : ℕ) : Finset (Finset ℕ) :=
  (Icc 3 n).image (λ k => {k - 2, k - 1, k})

-- EXAMPLES
-- These use the Boolean checker.
#eval checkPreSolution 4 {{1, 2, 3}, {2, 3, 4}} -- true
#eval checkPreSolution 5 (naturalPreSolution 5) -- true

-- Fails because one set has card 2
#eval checkPreSolution 4 {{1, 2}, {2, 3, 4}}    -- false

/-
  TUTORIAL:
  1. We used 'Finset.image' above. Unlike 'map', 'image' doesn't require
     a proof of injectivity upfront, but it produces the same result
     here because each k creates a unique set.
  2. In 'checkPreSolution', we used 'filter (...) == ∅'.
     This is the most reliable way in Lean 4 to write a "for all"
     check that works inside #eval.
  3. 'Icc 3 n' is the Finset {3, 4, ..., n}.
-/
