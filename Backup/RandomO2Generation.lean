open List

----------------------------------------------------------------
-- 1. SYNCHRONIZED OPERATIONAL CORE
----------------------------------------------------------------

def satisfiesRule (hist : List (Nat × Nat × Nat)) (a b n : Nat) : Bool :=
  if (a == 1 || a == 2 || a == 3) && (b == 1 || b == 2 || b == 3) then
    true
  else if b > 3 && b ≤ n then
    hist.any (fun (x, y, z) =>
      z ≤ b && (
        (x == a && y == b) || (x == b && y == a) ||
        (x == a && z == b) || (x == b && z == a) ||
        (y == a && z == b) || (y == b && z == a)
      )
    )
  else
    false

def noThirdElementGreater3 (hist : List (Nat × Nat × Nat)) (a b : Nat) : Bool :=
  not (hist.any (fun (x, y, z) =>
    if (x == a && y == b) || (x == b && y == a) then z > 3
    else if (x == a && z == b) || (x == b && z == a) then y > 3
    else if (y == a && z == b) || (y == b && z == a) then x > 3
    else false
  ))

def isValidO2Provable (fuel : Nat) (input : List (Nat × Nat × Nat)) : Bool :=
  match input with

  | [] => true
  | (a, b, c) :: tail =>
    match fuel with

    | 0 => false
    | f + 1 =>
      if tail.isEmpty && a == 1 && b == 2 && c == 3 then
        true
      else if not (isValidO2Provable f tail) then
        false
      else
        let n := c - 1
        let (inA, inB) := if a < b then (a, b) else (b, a)
        let allPairs : List (Nat × Nat) :=
          tail.flatMap (fun (x, y, z) =>
            [(x, y), (y, z), (x, z)].map (fun (u, v) => if u < v then (u, v) else (v, u))
          )
        allPairs.any (fun (u, v) =>
          u == inA && v == inB && satisfiesRule tail u v n && noThirdElementGreater3 tail u v
        )

def historyPairs (hist : List (Nat × Nat × Nat)) : List (Nat × Nat) :=
  ((hist.flatMap (fun (x, y, z) =>
    [(x, y), (y, z), (x, z)].map (fun (u, v) => if u < v then (u, v) else (v, u))
  ))).eraseDups

def getValidChoices (hist : List (Nat × Nat × Nat)) (currentN : Nat) : List (Nat × Nat) :=
  (historyPairs hist).filter (fun (a, b) =>
    satisfiesRule hist a b (currentN - 1) && noThirdElementGreater3 hist a b
  )

----------------------------------------------------------------
-- 2. RANDOM SAMPLING ALGORITHM (SUBTRACTION-FREE OFFSETS)
----------------------------------------------------------------

partial def generateRandomO2Step (currentHistory : List (Nat × Nat × Nat)) (currentK targetK : Nat) : IO (List (Nat × Nat × Nat)) := do
  if currentK > targetK then
    return currentHistory
  else
    let allPairs := historyPairs currentHistory

    let validChoices := allPairs.filter (fun (a, b) =>
      satisfiesRule currentHistory a b (currentK + 3) && noThirdElementGreater3 currentHistory a b
    )

    match validChoices with

    | [] =>
      generateRandomO2Step currentHistory (currentK + 1) targetK
    | _ =>
      let randomIndex ← IO.rand 0 (validChoices.length - 1)
      -- Fixed: Using core-supported macro list index brackets lookup instead of .get!
      let (chosenA, chosenB) := validChoices[randomIndex]!

      let nextHistory := (chosenA, chosenB, currentK + 4) :: currentHistory
      generateRandomO2Step nextHistory (currentK + 1) targetK

def generateRandomO2 (targetK : Nat) : IO (List (Nat × Nat × Nat)) := do
  generateRandomO2Step [(1, 2, 3)] 0 targetK

--- Simulation Trace Runs ---
-- Fixed: Core Lean 4 handles IO evaluation perfectly under #eval natively
#eval generateRandomO2 2
#eval generateRandomO2 5
#eval generateRandomO2 10
