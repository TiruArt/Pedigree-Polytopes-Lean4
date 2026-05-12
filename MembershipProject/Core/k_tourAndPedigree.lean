import Mathlib.Data.List.Basic


/--
  Performs one step of growth.
  Returns `Except.error` if the target edge is not in the current list L.
-/
abbrev Edge := Nat × Nat
def growStep (L : List Edge) (target : Edge) (k : Nat) : Except String (List Edge) :=
  -- We check both (i, j) and (j, i) to be robust
  let targetRev := (target.2, target.1)
  if L.contains target then
    Except.ok ([(target.1, k), (target.2, k)] ++ L.erase target)
  else if L.contains targetRev then
    Except.ok ([(targetRev.1, k), (targetRev.2, k)] ++ L.erase targetRev)
  else
    Except.error s!"Error at k={k}: Edge {target} is not in the current Available_edges L."

/--
  Recursively processes the list P to grow L from k to n.
-/
def grow (k : Nat) (n : Nat) (L : List Edge) (P : List Edge) : Except String (List Edge) :=
  if k > n then
    Except.ok L
  else
    match P with

    | [] => Except.error s!"Error at k={k}: P is too short for n={n}."
    | p :: ps => do
        let nextL ← growStep L p k
        grow (k + 1) n nextL ps

-- --- TEST SUITE ---

def initialL : List Edge := [(1, 2), (1, 3), (2, 3)]

def runTest (n : Nat) (P : List Edge) : String :=
  match grow 4 n initialL P with

  | Except.ok L => s!"Is a Pedigree. (n={n}): Edges in {n}-tour = {L}"
  | Except.error e => s!"Failed! Not a Pedigree.  (n={n}): {e}"
/-- Sorts the boundary list L into a continuous k-tour starting from 'curr' --/
def sortCycle (L : List Edge) (curr : Nat) : List Edge :=
  match h_L : L with

  | [] => []
  | edges =>
    match h_find : edges.find? (λ e => e.1 == curr || e.2 == curr) with

    | none => []
    | some edge =>
      let nextV := if edge.1 == curr then edge.2 else edge.1
      let remaining := edges.erase edge
      have : remaining.length < L.length := by
        rw [h_L]; let h_mem := List.mem_of_find?_eq_some h_find
        rw [List.length_erase_of_mem h_mem]; apply Nat.sub_lt
        · apply List.length_pos_of_mem h_mem
        · exact Nat.zero_lt_one
      (curr, nextV) :: sortCycle remaining nextV
termination_by L.length

/-- Combined test runner: Grows the graph and then sorts the k-tour --/
def runTest_order (n : Nat) (P : List Edge) : String :=
  let initialL : List Edge := [(1, 2), (2, 3), (3, 1)]
  match grow 4 n initialL P with

  | Except.error e => s!"Failed: {e}"
  | Except.ok L =>
      let tour := sortCycle L 1
      s!"Success! n={n}. Sorted k-tour: {tour}"

/--
  Converts a sorted list of edges [(1, 4), (4, 2), (2, 1)]
  into a string "1 -> 4 -> 2 -> 1"
--/
def prettyPrint (tour : List Edge) : String :=
  match tour with

  | [] => "Empty Tour"
  | edges =>
      let nodes := edges.map (λ e => s!"{e.1}")
      let lastNode := s!"{edges.getLast!.2}"
      " -> ".intercalate (nodes ++ [lastNode])

/-- Combined test runner with Pretty Printing --/
def runTest_pretty (n : Nat) (P : List Edge) : String :=
  let initialL : List Edge := [(1, 2), (2, 3), (3, 1)]
  match grow 4 n initialL P with

  | Except.error e => s!"Failed: {e}"
  | Except.ok L =>
      let tour := sortCycle L 1
      s!"Success! n={n}K-Tour: {prettyPrint tour}"

-- --- Tests ---

-- n=6 example
#eval runTest_pretty 6 [(1, 2), (1, 3), (2, 3)]
-- Output: "Success! n=6\nK-Tour: 1 -> 4 -> 2 -> 6 -> 3 -> 5 -> 1"

-- n=4 example
#eval runTest_pretty 4 [(1, 2)]
-- Output: "Success! n=4\nK-Tour: 1 -> 4 -> 2 -> 3 -> 1"
-- --- Examples ---

-- Valid n=6
#eval runTest_pretty 6 [(1, 2), (1, 3), (2, 3)]

-- Valid n=7 (corrected from your previous example)
#eval runTest_pretty 7 [(1, 3), (3, 4), (1, 4), (4, 5)]

-- Incorrect P (using a non-existent edge)
#eval runTest 5 [(1, 2), (9, 9)]
-- 1. Valid P for n=4
#eval runTest 4 [(1, 2)]

-- 2. Valid P for n=5
#eval runTest 5 [(1, 2), (1, 4)]

-- 3. The invalid P from your example (n=7)
-- Fails because (1, 3) is used twice
#eval runTest 7 [(1, 3), (3, 4), (1, 3), (4, 5)]

-- 4. A corrected version for n=7
-- We replace (1,3), then (3,4), then (1,4), then (4,5)
#eval runTest 7 [(1, 3), (3, 4), (1, 4), (4, 5)]

-- 5. Not a valid P for n=8
#eval runTest 8 [(1, 2), (2, 3), (1, 3), (1, 4), (1, 5)]

-- 6. P is too short
#eval runTest 6 [(1, 2)]
-- 7. P is in P_{7}
#eval runTest 7 [(1, 2), (2,4), (2, 5), (5, 6)]
-- 8. P is not in P_{7}
#eval runTest 7 [(1, 2), (2,4), (2, 5), (3, 6)]
-- 9. P is too short
#eval runTest_order 6 [(1, 2)]
-- 10. P is in P_{7}
#eval runTest_order 7 [(1, 2), (2,4), (2, 5), (5, 6)]
-- 11. P is not in P_{7}
#eval runTest_order 7 [(1, 2), (2,4), (2, 5), (3, 6)]
-- 12. P is in P_{8}
#eval runTest_order 8 [(1, 2), (2, 3), (1, 3), (1, 4), (1, 5)]
-- 13. Not a valid P for n=8
#eval runTest_order 8 [(1, 2), (2, 3), (1, 3), (1, 4), (2, 5)]
