-- N_Check2Pedigree.lean
import MembershipProject.Core.N_HypSum
import MembershipProject.Core.N_EdgeInKTour
import MembershipProject.Core.LearningFinsetDesirableDef
import Mathlib.Tactic

namespace MembershipProject.Core

open Finset

def cyclicLeft (l : List ℕ) (idx : ℕ) : ℕ :=
  l.getD ((idx + l.length - 1) % l.length) 0

def cyclicRight (l : List ℕ) (idx : ℕ) : ℕ :=
  l.getD ((idx + 1) % l.length) 0

def hcFindIdx (l : List ℕ) (v : ℕ) : ℕ :=
  l.findIdx (· == v)

def cyclicNeighbors (l : List ℕ) (v : ℕ) : ℕ × ℕ :=
  let idx := hcFindIdx l v
  (cyclicLeft l idx, cyclicRight l idx)

def extractTriangle (hc : List ℕ) (k : ℕ) : Triple × List ℕ :=
  let (left, right) := cyclicNeighbors hc k
  let t := (min left right, max left right, k)
  (t, hc.filter (· ≠ k))

def hcToTriangles (hc : List ℕ) : List Triple :=
  let n := hc.length
  let rec go (hc : List ℕ) (k : ℕ) (acc : List Triple) : List Triple :=
    if k < 4 then acc
    else
      let (t, hc') := extractTriangle hc k
      go hc' (k - 1) (t :: acc)
  termination_by k
  [(1, 2, 3)] ++ go hc n []

def tripleToFinset (t : Triple) : Finset ℕ :=
  {t.1, t.2.1, t.2.2}

def triplesToFinsetFinset (ts : List Triple) : Finset (Finset ℕ) :=
  (ts.map tripleToFinset).toFinset

def partialHC (k i j : ℕ) : List ℕ :=
  [i, j] ++ ((List.range (k - 1)).filter (fun v => v + 1 ≠ i ∧ v + 1 ≠ j)
             |>.map (· + 1))

def partialTriangleList (k i j : ℕ) : List Triple :=
  hcToTriangles (partialHC k i j)

-- ============================================================
-- BASE CASE: k = 4, n > k > j > i >= 1
-- ============================================================

lemma partialTriangleList_k4 (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hjk : j < 4) :
    checkDesiredSolution 3
      (triplesToFinsetFinset (partialTriangleList 4 i j)) = true := by
  have hi2 : i ≤ 2 := by omega
  have hj3 : j ≤ 3 := by omega
  interval_cases i <;> interval_cases j <;> native_decide

-- ============================================================
-- INDUCTIVE STEP
-- ============================================================

lemma partialTriangleList_step (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k)
    (ih : checkDesiredSolution (k-1)
        (triplesToFinsetFinset (partialTriangleList k i j)) = true) :
    checkDesiredSolution k
        (triplesToFinsetFinset (partialTriangleList (k+1) i j)) = true := by
  -- partialHC (k+1) i j has k+1 removed from partialHC k i j... wait
  -- partialHC (k+1) i j = [i,j] ++ rest on {1,...,k}
  -- hcToTriangles adds triangle at layer k (neighbors of k in HC)
  -- Since n > k > j > i >= 1 is maintained, the new triangle is valid
  sorry -- [step] inductive extension of HC

-- ============================================================
-- MAIN THEOREM: partialTriangleList k i j is a valid pedigree
-- ============================================================

theorem partialTriangleList_isDesiredSolution (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) :
    checkDesiredSolution (k-1)
      (triplesToFinsetFinset (partialTriangleList k i j)) = true := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk4 : k = 4
    · subst hk4
      exact partialTriangleList_k4 i j hi hij hjk
    · -- k ≥ 5
      have hk5 : 5 ≤ k := by omega
      have hk5' : 4 ≤ k - 1 := by omega
      -- j < k and k ≥ 5: either j < k-1 (use IH) or j = k-1
      -- But partialPedigree is only called when isDefault(i,j,k) = false
      -- i.e. NOT (i = k-2 AND j = k-1), so we cannot have j = k-1 AND i = k-2
      -- However j could still equal k-1 with i < k-2
      -- For the induction: j < k gives j ≤ k-1
      -- We need j < k-1 for the IH at k-1
      -- Since i < j < k and i ≥ 1, if j = k-1 then i < k-1
      -- In that case partialTriangleList k i (k-1) is still valid by construction
      -- The IH at k-1 with j' = j requires j < k-1
      -- Handle j = k-1 separately by native_decide is not possible for general k
      -- Key insight: for the IH we use a DIFFERENT j' = j if j < k-1
      -- or the base case handles j = k-1
      by_cases hjk' : j < k - 1
      · have ih' := ih (k-1) (by omega) hk5' hjk'
        have hstep := partialTriangleList_step (k-1) i j hk5' hi hij hjk' ih'
        simp only [show k - 1 + 1 = k from by omega] at hstep
        exact hstep
      · -- j = k-1: partialHC k i (k-1) starts [i, k-1, ...]
        -- The pedigree is still valid, prove directly
        have hjk_eq : j = k - 1 := by omega
        subst hjk_eq
        -- Use strong induction differently: both i and j=k-1 are fixed
        -- The construction always gives a valid pedigree
        sorry -- [j=k-1 case]

end MembershipProject.Core
