 -- This file defines the ValidTriplets inductive type and the generateTriplets function
import Mathlib.Data.List.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.FinEnum
import Mathlib.Tactic
set_option linter.unusedVariables false

lemma sub_succ_lt_self (n k : Nat) (h1 : k < n) : n - (k + 1) < n - k := by
  omega

-- A helper to check the basic 1 <= i < j < k <= n condition
def IsOrderedTriplet (n : Nat) (t : Nat × Nat × Nat) : Prop :=
  let (i, j, k) := t
  1 ≤ i ∧ i < j ∧ j < k ∧ k ≤ n ∧ k >=3
inductive ValidTriplets : Nat → List (Nat × Nat × Nat) → Prop where
  -- Base case: n=3, the list must contain (1, 2, 3)

  | base : ValidTriplets 3 [(1, 2, 3)]

  -- Inductive step: moving from k to k+1
  | step (k : Nat) (L : List (Nat × Nat × Nat))
    (h_prev : ValidTriplets k L)
    (new_triplets : List (Nat × Nat × Nat))
    -- Rule: (a, b, k+1) is in new_triplets IFF b > 3 AND
    -- (some_x, a, b) or (a, some_x, b) was in the previous list L
    (h_iff : ∀ a b, (a, b, k + 1) ∈ new_triplets ↔
      (b > 3 ∧ ∃ x, (x, a, b) ∈ L ∨ (a, x, b) ∈ L))
    : ValidTriplets (k + 1) (L ++ new_triplets)

-- Define the core triplet type
def Triplet := Nat × Nat × Nat

-- Define the missing logic helpers first
def exists_match (acc : List (Nat × Nat × Nat)) (a b : Nat) : Bool :=
  acc.any (fun (x, y, z) => (x == a && y == b) || (y == a && z == b) || (x == a && z == b))

def exists_previous_k (acc : List (Nat × Nat × Nat)) (a b k_val : Nat) : Bool :=
  acc.any (fun (x, y, z) => x == a && y == b && z < k_val)


def exists_previous_k_ge4 (acc : List (Nat × Nat × Nat)) (a b : Nat) : Bool :=
  acc.any (fun (x, y, z) => x == a && y == b && z >= 4)

def generateTriplets (n : Nat) : List (Nat × Nat × Nat) :=
  let rec loop (k : Nat) (acc : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
    if hk : k > n then
      acc
    else if k = 4 then
      -- k=4 can use (1, 2) even though k=3 used it, because z < 4 previously.
      loop (k + 1) (acc ++ [(1, 2, 4)])
    else if k > 4 then
      let found := (List.range k).findSome? (fun b =>
        if b > 3 then
          (List.range b).findSome? (fun a =>
            -- a > 0, a != 3, b > 3.
            -- exists_match checks if they appeared together ANYWHERE before.
            -- !exists_previous_k_ge4 ensures (a, b) hasn't been the "lead pair" for any k >= 4.
            if a > 0 && a != 3 && exists_match acc a b && !exists_previous_k_ge4 acc a b then
              some (a, b, k)
            else none
          )
        else none
      )
      match found with

      | some tri => loop (k + 1) (acc ++ [tri])
      | none     => loop (k + 1) acc
    else
      loop (k + 1) acc
  termination_by n + 1 - k
  decreasing_by all_goals (simp_all; omega)

  loop 3 [(1, 2, 3)]

def P : List (Nat × Nat × Nat) := generateTriplets 8
#eval P



-- Examples
#eval! generateTriplets 4
#eval! generateTriplets 5
#eval! generateTriplets 9
#eval! generateTriplets 10
