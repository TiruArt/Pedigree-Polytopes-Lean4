open List

partial def O2 : Nat → List (Nat × Nat × Nat)

  | 0 => []
  | 1 => []
  | 2 => []

  | 3 => [(1, 2, 3)]
  | n + 1 =>
    let allPairs : List (Nat × Nat) :=
      (range (n + 1)).flatMap (fun m =>
        (O2 m).flatMap (fun (x, y, z) =>
          [(x, y), (y, z), (x, z)].map (fun (u, v) => if u < v then (u, v) else (v, u))
        )
      )

    let satisfiesRule (a b : Nat) : Bool :=
      if (a == 1 || a == 2 || a == 3) && (b == 1 || b == 2 || b == 3) then
        true
      else if b > 3 && b ≤ n then
        -- Enforced: b is exactly the second/larger element of the pair (a, b)
        -- We check O2 b directly to see if {r, a, b} exists as a triple
        (O2 b).any (fun (x, y, z) =>
          (x == a && y == b) || (x == b && y == a) ||
          (x == a && z == b) || (x == b && z == a) ||
          (y == a && z == b) || (y == b && z == a)
        )
      else
        false

    let noThirdElementGreater3 (a b : Nat) : Bool :=
      not ((range (n + 1)).any (fun m =>
        (O2 m).any (fun (x, y, z) =>
          if (x == a && y == b) || (x == b && y == a) then z > 3
          else if (x == a && z == b) || (x == b && z == a) then y > 3
          else if (y == a && z == b) || (y == b && z == a) then x > 3
          else false
        )
      ))

    match allPairs.find? (fun (a, b) => satisfiesRule a b && noThirdElementGreater3 a b) with

    | some (a, b) => (a, b, n + 1) :: O2 n
    | none        => O2 n

--- Verification Tests ---
#eval O2 4
#eval O2 5
#eval O2 6
#eval O2 7
#eval O2 8
#eval O2 9
#eval O2 10
