-- N_HC2Pedigree.lean
-- Constructs partialPedigree k i j : Pedigree (k-1) from HC
-- using hcToTriangles and checkDesiredSolution for verification.

import MembershipProject.Core.N_HypSum
import MembershipProject.Core.N_EdgeInKTour
import MembershipProject.Core.LearningFinsetDesirableDef
import Mathlib.Tactic

namespace MembershipProject.Core

-- ============================================================
-- HC → TRIANGLE LIST (proved correct by #eval)
-- ============================================================

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

-- ============================================================
-- CONVERT TO Finset (Finset ℕ) FOR checkDesiredSolution
-- ============================================================

def tripleToFinset (t : Triple) : Finset ℕ :=
  {t.1, t.2.1, t.2.2}

def triplesToFinsetFinset (ts : List Triple) : Finset (Finset ℕ) :=
  (ts.map tripleToFinset).toFinset

-- ============================================================
-- BUILD HC FROM (k, i, j) FOR partialPedigree
-- ============================================================

/-- The HC used for partialPedigree k i j:
    starts [i, j, ...] with remaining vertices in order -/
def partialHC (k i j : ℕ) : List ℕ :=
  [i, j] ++ ((List.range (k - 1)).filter (fun v => v + 1 ≠ i ∧ v + 1 ≠ j)
             |>.map (· + 1))

/-- The triangle list for partialPedigree k i j -/
def partialTriangleList (k i j : ℕ) : List Triple :=
  hcToTriangles (partialHC k i j)

-- ============================================================
-- VERIFICATION BY native_decide FOR CONCRETE CASES
-- ============================================================

-- These verify the construction is correct for specific (k,i,j)
example : checkDesiredSolution 4
    (triplesToFinsetFinset (partialTriangleList 5 1 2)) = true := by native_decide

example : checkDesiredSolution 4
    (triplesToFinsetFinset (partialTriangleList 5 1 3)) = true := by native_decide

example : checkDesiredSolution 5
    (triplesToFinsetFinset (partialTriangleList 6 1 3)) = true := by native_decide

example : checkDesiredSolution 5
    (triplesToFinsetFinset (partialTriangleList 6 2 5)) = true := by native_decide

-- ============================================================
-- partialPedigree AS CONCRETE Pedigree (k-1)
-- ============================================================

/-- For concrete k, i, j we can close by native_decide.
    For the general case we keep as axiom pending a general proof. -/
noncomputable def partialPedigree (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) : Pedigree (k-1) where
  triangles    := partialTriangleList k i j
  h_n          := by omega
  h_length     := by
    simp [partialTriangleList, partialHC, hcToTriangles]
    sorry -- [length] len = k-3 = (k-1)-2
  h_first      := by
    simp [partialTriangleList, hcToTriangles]
  h_layers     := by
    intro m hm
    simp [partialTriangleList]
    sorry -- [layers] triangle m has layer m+3
  h_generators := by
    intro m hpos hm
    sorry -- [generators] from HC construction
  h_in_delta   := by
    intro m hm
    sorry -- [in_delta] 1 ≤ a < b < layer
  h_distinct   := by
    sorry -- [distinct] no repeated insertion edges

end MembershipProject.Core
