-- This file defines the functions to find the discordant indices
-- between two lists and to perform the swap operation on a list based on a given set of indices. It also includes example usage of these functions.

import Init.Data.List.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.FinEnum
def findDiscords {α : Type} [DecidableEq α] (P Q : List α) : List Nat :=
  -- Zip first, then use mapIdx to get the index (i) and pairs (p, q)
  (List.zip P Q).mapIdx (fun i (p, q) => if p ≠ q then some i else none)
  |>.filterMap id

-- Example usage:
-- #eval findDiscords [1, 2, 3, 4] [1, 5, 3, 6] -- Output: [1, 3]



def Swap_List {α : Type} (P Q : List α) (C : List Nat) : List α :=
  ((List.range P.length).zip P).zip Q |>.map (fun ((i, p_val), q_val) =>
    if i ∈ C then q_val else p_val
  )

-- Example usage
def P1 := [(1,2,3), (1,2,4), (1,3,5), (2,3,6), (3,4,7)]
def Q1 := [(1,2,3), (1,3,4), (3,4,5), (2,3,6), (4,5,7)]
def D1 := findDiscords P1 Q1

def P2 := [(1,2,3), (1,2,4), (1,4,5), (2,3,6)]
def Q2 := [(1,2,3), (1,3,4), (1,4,5), (4,5,6)]
def D2 := findDiscords P2 Q2
def C1:List Nat := findDiscords P1 Q1
def C2:List Nat := {3}
def R1:= Swap_List P1 Q1 C1
def R2:= Swap_List P2 Q2 C2

def checkAdjacent {α : Type} [DecidableEq α] (R Q : List α) : IO Unit :=
  if R = Q then
    IO.println "adjacent"
  else
    IO.println "non-adjacent"

-- Usage:
#eval findDiscords P1 Q1 -- Output: [1, 2, 4]
#eval findDiscords P2 Q2 -- Output: [1, 3]
#eval checkAdjacent R1 Q1 -- Outputs: adjacent
#eval checkAdjacent R2 Q2 -- Outputs: non-adjacent


#eval Swap_List P1 Q1 C1 -- Output: [(1, 2, 3), (1, 3, 4), (3, 4, 5), (2, 3, 6)]
#eval Swap_List P2 Q2 C2 -- Output: [(1, 2, 3), (1, 2, 4), (1, 4, 5), (4, 5, 6)]
