open List

def satisfiesRule (hist : List (Nat × Nat × Nat)) (a b n : Nat) : Bool :=
  if (a == 1 || a == 2 || a == 3) && (b == 1 || b == 2 || b == 3) then
    true
  else if b > 3 && b ≤ n then
    -- Enforced: We filter the history list so that the triple MUST
    -- belong to the generation history at or before step b (z ≤ b)
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

partial def isValidO2Any (input : List (Nat × Nat × Nat)) : Bool :=
  match input with

  | [] => true
  | [(1, 2, 3)] => true
  | (a, b, c) :: tail =>
    if not (isValidO2Any tail) then false
    else
      let n := c - 1
      -- Ensure u < v so that v is strictly the larger element (b = max(a, b))
      let (inA, inB) := if a < b then (a, b) else (b, a)

      let allPairs : List (Nat × Nat) :=
        tail.flatMap (fun (x, y, z) =>
          [(x, y), (y, z), (x, z)].map (fun (u, v) => if u < v then (u, v) else (v, u))
        )

      allPairs.any (fun (u, v) =>
        u == inA && v == inB && satisfiesRule tail u v n && noThirdElementGreater3 tail u v
      )

--- Verification Tests ---

-- 1. The original valid O2 6 sequence
#eval isValidO2Any [(1, 3, 6), (2, 3, 5), (1, 2, 4), (1, 2, 3)]
-- Returns: true

-- 2. Testing your example with the structural constraint rule enforced:
#eval isValidO2Any [(1, 2, 6), (2, 4, 5), (1, 3, 4), (1, 2, 3)]
-- Returns: false
