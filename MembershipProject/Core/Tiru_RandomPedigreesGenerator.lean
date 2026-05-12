import Lean

-- Define the triplet type
structure Triplet (n : Nat) where
  (i j k : Nat)
deriving Repr, BEq

-- Helper to check if (a, b) was part of a previous triplet as (x, a, b) or (a, x, b)
def existsDependency ( n:Nat)(triplets : List (Triplet n)) (a b : Nat) : Bool :=
  triplets.any (λ t => (t.i == a && t.k == b) || (t.j == a && t.k == b))

-- Helper to check if (a, b) was already used as the start of a triplet for l >= 4
def alreadyUsed ( n:Nat)(triplets : List (Triplet n)) (a b : Nat) : Bool :=
  triplets.any (λ t => t.k >= 4 && t.i == a && t.j == b)

-- Main generation function
partial def generateTriplets (n : Nat) : IO (List (Triplet n)) := do
  let mut triplets : List (Triplet n) := [⟨1, 2, 3⟩]

  for k in [4:n+1] do
    let mut candidates : List (Nat × Nat) := []
    for a in [1:k] do
      for b in [a+1:k] do
        -- Condition for k=4
        if k == 4 then
          if a <= 3 && b <= 3 then candidates := (a, b) :: candidates
        else
          -- Condition for k > 4
          let hasDep := existsDependency n triplets a b
          let notUsed := !(alreadyUsed n triplets a b)
          if ((b > 3) && hasDep && (notUsed)) then
            candidates := (a, b) :: candidates

    if candidates.isEmpty then
      throw (IO.userError "No valid triplets possible for current n")

    -- Randomly pick one candidate
    let idx ← IO.rand 0 (candidates.length - 1)
    let candidatesArray := candidates.toArray
    let (a, b) := candidatesArray[idx]!

    triplets := List.append triplets [⟨a, b, k⟩]

  return triplets

-- Example Usage
#eval show IO Unit from do
  for l in [3:10] do
    for s in [1:3] do
      let result ← generateTriplets l
      IO.println s!"Generated List: {l}, P_{s}: {repr result }"
