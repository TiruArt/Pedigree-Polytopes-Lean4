-- 1. IMPORTS FIRST
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat




open Finset
-- 1. FIX: A Computable Printing Rule
-- We don't use 'toList'. Instead, we check which numbers from 1 to 20 are in the set.
-- This is 100% computable and won't cause the error!
noncomputable instance : Repr (Finset ℕ) where
  reprPrec s _ := repr ((List.range 21).filter (λ x => x ∈ s))

-- 2. FIX: A Printing Rule for the Set of Sets
-- We convert the outer Finset to a List just for the display loop.
noncomputable instance : Repr (Finset (Finset ℕ)) where
  reprPrec S _ := repr (S.val.toList.map (λ t => t))
-- 4. YOUR DEFINITIONS
def S3 : Finset (Finset ℕ) := {{1, 2, 3}}

/--
  PREDICATE: isPreSolution
  Using n as a parameter allows us to use the same 'Finset (Finset ℕ)' type
  for any n, carrying the bounds as a logical requirement.
-/
def isPreSolution (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  S.card = n - 2 ∧
  (∀ t ∈ S, t.card = 3) ∧
  (∀ k ∈ Icc 3 n, ∃! t ∈ S, t.max = some k) ∧
  (∀ t ∈ S, ∀ x ∈ t, x ≤ n)

/--
  CHECKER: checkPreSolution
  Replaced .all with 'filter == ∅' to ensure it compiles and evaluates.
-/
def checkPreSolution (n : ℕ) (S : Finset (Finset ℕ)) : Bool :=
  let correct_count := S.card == n - 2
  -- Rule: No triplets should have card != 3
  let all_triplets := S.filter (λ t => t.card != 3) == ∅
  -- Rule: No k in range should have other than 1 triplet
  let all_maxes := (Icc 3 n).filter (λ k => (S.filter (λ t => t.max == some k)).card != 1) == ∅
  -- Rule: No number x in any triplet t should be > n
  let within_bounds := S.filter (λ t => (t.filter (λ x => x > n)) != ∅) == ∅

  correct_count && all_triplets && all_maxes && within_bounds

/--
  A "Natural" construction that works for any n.
  By using .image, we avoid the need for an injectivity proof.
-/
def naturalPreSolution (n : ℕ) : Finset (Finset ℕ) :=
  if n < 3 then ∅ else (Icc 3 n).image (λ k => {k - 2, k - 1, k})

-- TESTING COMPATIBILITY
def S4 := naturalPreSolution 4 -- {{1,2,3}, {2,3,4}}
def S5 := naturalPreSolution 5 -- {{1,2,3}, {2,3,4}, {3,4,5}}

#eval checkPreSolution 4 S4 -- true
#eval checkPreSolution 5 S5 -- true

-- Demonstrating that we can combine them because they are the same TYPE
def combined := S4 ∪ S5
#eval combined.card -- 3 (because {1,2,3} and {2,3,4} are shared)
-- Assume S4 is already defined as S4 ={{1,2,3}, {2,3,4}}


/--
  We extend S4 by adding the triplet for k = 5.
  Note: 'insert' is the standard way to add an element to a Finset.
-/
def S4_extended_to_5 : Finset (Finset ℕ) :=
  insert {3, 4, 5} S4

-- Now let's verify it
#eval checkPreSolution 5 S4_extended_to_5 -- Result: true

/--
  Generalizing this: A function that takes a pre-solution for n
  and "grows" it to n+1 by adding a specific choice for the new max.
-/
def growPreSolution (n : ℕ) (S : Finset (Finset ℕ)) (newTriplet : Finset ℕ) : Finset (Finset ℕ) :=
  insert newTriplet S

-- Example: Growing S4 with a "random" choice for k=5
-- The only rule for a pre-solution is that the max must be 5 and card must be 3.
def S5_custom := growPreSolution 4 S4 {1, 2, 5}

#eval checkPreSolution 5 S5_custom -- Result: true
/--
  Recursively extends a pre-solution S from n up to target_m.
  For each new k, it adds the "natural" triplet {k-2, k-1, k}.
-/
def extendTo (target_m : ℕ) (S : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  match target_m with

  | 0 | 1 | 2 => S -- Pre-solutions only start from n=3
  | m + 1 =>
      let S_prev := extendTo m S
      -- If m+1 is not yet represented as a maximum, add its natural triplet
      if (S_prev.filter (λ t => t.max == some (m + 1))).card == 0 then
        insert {m - 1, m, m + 1} S_prev
      else
        S_prev

-- Let's see it in action!



#eval checkPreSolution 3 S3 -- true
#eval checkPreSolution 6 (extendTo 6 S3) -- true!
#eval checkPreSolution 6 (extendTo 6 S3)

-- 1. The Computable Check (Yes/No)
-- If this returns true, your logic for extendTo 6 is correct.
#eval checkPreSolution 6 (extendTo 6 S3)

-- 2. The "Hard" Verification (Proof)
-- This tells the compiler: "Run the boolean check, and if it's true,
-- I accept it as a proof."
example : checkPreSolution 6 (extendTo 6 S3) = true :=
  rfl

def getSortedList [LinearOrder ℕ] (s : Finset ℕ) : List ℕ :=
  -- Use '<=' or '<' as the ordering relation
  s.sort (· ≤ ·)

#eval getSortedList ({3, 1, 4, 2} : Finset ℕ)
-- Output: [1, 2, 3, 4]


