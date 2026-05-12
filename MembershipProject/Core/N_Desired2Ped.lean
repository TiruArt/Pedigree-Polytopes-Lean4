-- N_Desired2Ped.lean
-- isDesiredSolution → Pedigree

import MembershipProject.Core.N_HypSum
import MembershipProject.Core.LearningFinsetDesirableDef
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic

namespace MembershipProject.Core

open Finset

-- Error 1: finsetToLst must be noncomputable
noncomputable def finsetToLst (s : Finset (Finset ℕ)) : List (Finset ℕ) :=
  s.toList

noncomputable def finsetToTriple (s : Finset ℕ) : Triple :=
  let lst := s.sort (· ≤ ·)
  (lst.getD 0 0, lst.getD 1 0, lst.getD 2 0)

noncomputable def sortByMax (l : List (Finset ℕ)) : List (Finset ℕ) :=
  l.mergeSort (fun s t => s.max.getD 0 ≤ t.max.getD 0)

noncomputable def desiredToTripleList (S : Finset (Finset ℕ)) : List Triple :=
  (sortByMax (finsetToLst S)).map finsetToTriple

-- Error 2,3,4: h_n and h_length need correct lemmas
-- Finset.card_toList: S.toList.length = S.card
-- List.length_mergeSort: preserves length
-- List.length_map: length of map

noncomputable def desiredToPedigree (n : ℕ) (hn : 3 ≤ n) (S : Finset (Finset ℕ))
    (h : isDesiredSolution n S) : Pedigree n where
  triangles  := desiredToTripleList S
  h_n        := by
    exact hn
  h_length   := by
    simp only [desiredToTripleList, List.length_map]
    simp only [sortByMax, List.length_mergeSort]
    simp only [finsetToLst]
    -- S.toList.length = S.card = n-2
    rw [Finset.length_toList]
    exact h.1.1.1
  h_first    := by
    sorry -- [first]
  h_layers   := by
    intro m hm
    sorry -- [layers]
  h_generators := by
    intro m hpos hm
    sorry -- [generators]
  h_distinct := by
    intro i j hi hj hipos hjpos hne
    sorry -- [distinct]
  h_in_delta := by
    intro m hm
    sorry -- [in_delta]

end MembershipProject.Core
