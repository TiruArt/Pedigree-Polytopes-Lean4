
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card -- Necessary for the .card property
import Mathlib.Data.Finset.Insert -- This provides the 'insert' logic
set_option linter.unusedVariables false
/-- A 3-element subset of {1, ..., n} -/
def ThreeElementSubset (n : Nat) :=
  { s : Finset Nat // s.card = 3 ∧ ∀ x ∈ s, 1 ≤ x ∧ x ≤ n }

-- Example construction for n = 5
def myExampleSet : ThreeElementSubset 5 :=
  ⟨{1, 2, 3}, by decide⟩
/-- Generates a random 3-element array of unique numbers -/
def getRandom3Array (n : Nat) : IO (Array Nat) := do
  if n < 3 then throw (IO.userError "n must be at least 3")
  let mut arr : Array Nat := #[]
  while arr.size < 3 do
    let val ← IO.rand 1 n
    if !arr.contains val then
      arr := arr.push val
  return arr
/-- Generates a random sorted 3-element array of unique numbers from {1, ..., n} -/
def getRandomOrdered3Array (n : Nat) : IO (Array Nat) := do
  if n < 3 then throw (IO.userError "n must be at least 3")
  let mut arr : Array Nat := #[]
  while arr.size < 3 do
    let val ← IO.rand 1 n
    if !arr.contains val then
      arr := arr.push val
  -- Sort the array to make it an "ordered set"
  return arr.qsort (· < ·)
-- This will now print correctly because Array has a Repr instance
#eval getRandom3Array 10
#eval getRandomOrdered3Array 10

/-- If you need it as a Finset for your structure/proofs -/
def get3Finset (n : Nat) : IO (Finset Nat) := do
  let arr ← getRandom3Array n
  return {arr[0]!, arr[1]!, arr[2]!}
/-- Loop to print 5 random sets -/
def print5RandomSets (n : Nat) : IO Unit := do
  IO.println s!"Printing 5 random 3-element subsets of [1..{n}]:"
  for i in [0:5] do
    let res ← getRandom3Array n
    IO.println s!"Set {i + 1}: {res}"

#eval print5RandomSets 10
/-- Loop to print 5 random ordered sets -/
def print5OrderedSets (n : Nat) : IO Unit := do
  IO.println s!"Printing 5 random ordered 3-element subsets of [1..{n}]:"
  for i in [0:5] do
    let res ← getRandomOrdered3Array n
    -- Converting to string for a "set-like" look {a, b, c}
    IO.println s!"Set {i + 1}: {res.toList}"

#eval print5OrderedSets 10




/--
Generates a list of triples {i, j, k} for k = 3, ..., n
such that:
1. 1 <= i < j < k
2. All pairs (i, j) are distinct across the entire list.
-/


def getRandomUniqueTriples (n : Nat) : IO Unit := do
  IO.println s!"Selecting triples e_k = 'i, j, k' for k in [3..{n}] with distinct (i, j):"

  let mut usedPairs : List (Nat × Nat) := []

  for k in [3 : n + 1] do
    let mut possiblePairs : Array (Nat × Nat) := #[]
    for i in [1 : k] do
      for j in [i + 1 : k] do
        if !usedPairs.contains (i, j) then
          possiblePairs := possiblePairs.push (i, j)

    if possiblePairs.isEmpty then
      IO.println s!"  k = {k}: No unique pairs remaining!"
      break

    -- Pick one valid pair
    let idx ← IO.rand 0 (possiblePairs.size - 1)
    let (i, j) := possiblePairs[idx]!
    usedPairs := usedPairs.concat (i, j)

    -- Sort to ensure i < j < k for the printout
    let triple := [i, j, k].insertionSort (· < ·)
    IO.println s!"  e_{k} = '{triple[0]!}, {triple[1]!}, {triple[2]!}'"

#eval getRandomUniqueTriples 10
/-- Represents the pair e_k = {i, j} with constraints: 1 ≤ i < j < k -/
structure Ek (k : ℕ) where
  i : ℕ
  j : ℕ
  h_i : 1 ≤ i
  h_j : 2 ≤ j -- Derived from i < j and i ≥ 1, but stated explicitly
  h_order : i < j
  h_k : j < k
-- 1. How to print the Ek structure for a specific k
instance {k : ℕ} : Repr (Ek k) where
  reprPrec e _ := s!" (i: {e.i}, j: {e.j})"

-- 2. How to print the Sigma type (k paired with Ek k)
instance : Repr (Σ k, Ek k) where
  reprPrec s _ := reprPrec s.2 0 ++ s!" (k={s.1})"

-- 3. (Optional but better) How to format it as a String
instance : ToString (Σ k : ℕ, Ek k) where
  toString p := s!"e_{p.1}: ({p.2.i}, {p.2.j})"

/-- A valid list P of length (n-3) for k = 4, ..., n -/
structure ValidProcess (n : ℕ) where
  h_n : n ≥ 3
  -- A list of pairs (k, Ek k) for k from 4 to n
  pairs : List (Σ k : ℕ, Ek k)
  -- 1. Length must be n - 3
  h_len : pairs.length = n - 3
  -- 2. Indices must be exactly 4, ..., n
  h_indices : pairs.map (·.1) = List.range' 4 (n - 3)
  -- 3. All e_k must be distinct (as sets {i, j, k})
  h_distinct : List.Nodup (pairs.map (fun p => (({p.2.i, p.2.j, p.1} : Finset ℕ))))

  -- 4. Hierarchical constraint: if e_k = {i, l} and l > 3,
  -- there exists a prior e_l = {i, a} or i ∈ {1, 2, 3}
-- The corrected hierarchy constraint
  h_hierarchy : ∀ (p : Σ k : ℕ, Ek k), p ∈ pairs →
    let k := p.1
    let i := p.2.i
    let l := p.2.j
    (l > 3 → ∃ (p_prev : Σ k' : ℕ, Ek k'),
      p_prev ∈ pairs ∧ p_prev.1 = l ∧ p_prev.2.i = i)
    ∨ (l ≤ 3 ∧ (i = 1 ∨ i = 2 ∨ i = 3))

-- Example n = 6
def ex_n6 : ValidProcess 6 := {
  h_n := by linarith
  pairs := [
    ⟨4, { i := 1, j := 2, h_i := by decide, h_order := by decide, h_k := by decide, h_j := by decide }⟩,
    ⟨5, { i := 1, j := 4, h_i := by decide, h_order := by decide, h_k := by decide, h_j := by decide }⟩,
    ⟨6, { i := 1, j := 5, h_i := by decide, h_order := by decide, h_k := by decide, h_j := by decide }⟩
  ]
  h_len := rfl
  h_indices := rfl
  h_distinct := by decide
  h_hierarchy := by
    intro p h_in
    simp at h_in
    rcases h_in with h4 | h5 | h6
    · -- Case k=4
      subst h4; right; simp
    · -- Case k=5
      subst h5; left
      intro -- This clears the "l > 3 →" part
      use ⟨4, {i:=1, j:=2, h_i:=by decide, h_order:=by decide, h_k:=by decide, h_j := by decide }⟩
      simp
    · -- Case k=6
      subst h6; left
      intro -- This clears the "l > 3 →" part
      use ⟨5, {i:=1, j:=4, h_i:=by decide, h_order:=by decide, h_k:=by decide, h_j := by decide }⟩
      simp
}
-- Helper to create a triplet for a given k with proof placeholders
def mkPairSafe (k i j : Nat) : Option (Σ k : Nat, Ek k) :=
  if h1 : 1 ≤ i then
    if h2 : 2 ≤ j then
      if h3 : i < j then
        if h4 : j < k then
          some ⟨k, { i := i, j := j, h_i := h1, h_j := h2, h_order := h3, h_k := h4 }⟩
        else none
      else none
    else none
  else none

/-- Automatically finds a valid sequence of (i, j) for k = 4 to n -/
partial def findValidPairs (n : Nat) : Option (List (Σ k : Nat, Ek k)) :=
  let rec loop (k : Nat) (acc : List (Σ k : Nat, Ek k)) : Option (List (Σ k : Nat, Ek k)) :=
    if k > n then
      some acc.reverse
    else
      -- 1. Candidates for (i, j)
      let base_cases := [(1, 2), (1, 3), (2, 3)]
      let recursive := acc.map (fun p => (p.2.i, p.1))
      let all_choices := base_cases ++ recursive

      -- 2. Modified distinctness check: e_k must be a new PAIR {i, j}
      let valid_choice := all_choices.findSome? (fun (i, j) =>
        match mkPairSafe k i j with

        | some pair =>
            -- Check if this specific {i, j} pair has been used before as an e_m
            let new_pair : Finset Nat := {i, j}
            let is_pair_distinct := acc.all (fun p =>
              ({p.2.i, p.2.j} : Finset Nat) != new_pair)

            if is_pair_distinct then some pair else none
        | none => none)

      match valid_choice with

      | some pair => loop (k + 1) (pair :: acc)
      | none => none

  loop 4 []


-- Modified loop to include a pseudo-random seed
partial def findRandomPairs (n : Nat) (seed : Nat := 0) : Option (List (Σ k : Nat, Ek k)) :=
  let rec loop (k : Nat) (acc : List (Σ k : Nat, Ek k)) (rng : Nat) : Option (List (Σ k : Nat, Ek k)) :=
    if k > n then
      some acc.reverse
    else
      let base_cases := [(1, 2), (1, 3), (2, 3)]
      let recursive := acc.map (fun p => (p.2.i, p.1))
      let all_choices := base_cases ++ recursive

      -- Filter valid choices based on your distinctness and hierarchy rules
      let valid_candidates := all_choices.filter (fun (i, j) =>
        match mkPairSafe k i j with

        | some _ =>
            let new_pair : Finset Nat := {i, j}
            acc.all (fun p => ({p.2.i, p.2.j} : Finset Nat) != new_pair)
        | none => false)

      if h : valid_candidates.length > 0 then
        -- Simple pseudo-random index selection
        let idx := rng % valid_candidates.length
        -- Use the indexing notation [idx]! which is the standard Lean 4 way to get!
        let (i, j) := valid_candidates[idx]!

        -- Unwrapping the pair (we know it's valid because we filtered valid_candidates)
        match mkPairSafe k i j with

        | some pair =>
          let next_rng := (rng * 1103515245 + 12345) % (2^31)
          loop (k + 1) (pair :: acc) next_rng
        | none => none
      else
        none

  loop 4 [] 149



-- Example usage for n = 7
-- This converts the complex Option/Sigma type into a simple Option (List String)
#eval (findValidPairs 7).map (fun list => list.map toString)

/-- Formats a single ValidProcess result for the table -/
def formatLine (n : Nat) : String :=
  match findValidPairs n with

  | some pairs => s!"n={n} | " ++ (pairs.map toString |>.toString)
  | none      => s!"n={n} | No valid process found"

/-- Generates a table for n from 4 to 10 -/
def generateTable : String :=
  let ns := List.range' 4 7 -- Generates [4, 5, 6, 7, 8, 9, 10]
  let lines := ns.map formatLine
  "--- Triples Table (e_k: {i, j, k}) ---\n" ++ (lines.intersperse "\n" |>.foldl (· ++ ·) "")

#eval IO.println generateTable
/-- Formats a single ValidProcess result for the table -/
def formatRanLine (n : Nat) : String :=
  match findRandomPairs n with

  | some pairs => s!"n={n} | " ++ (pairs.map toString |>.toString)
  | none      => s!"n={n} | No valid process found"

/-- Generates a table for n from 4 to 10 -/
def generateRanTable : String :=
  let ns := List.range' 4 7 -- Generates [4, 5, 6, 7, 8, 9, 10]
  let lines := ns.map formatRanLine
  "--- Random Valid Triples Table (e_k: {i, j, k}) ---\n" ++ (lines.intersperse "\n" |>.foldl (· ++ ·) "")

#eval IO.println generateRanTable



-- VALIDATION FUNCTION
def isValidSequence (n : Nat) (triples : List (Σ k : Nat, Ek k)) : Bool :=
  -- Structural recursion on 'remaining' solves termination automatically
  let rec validate (remaining : List (Σ k : Nat, Ek k)) (acc : List (Σ k : Nat, Ek k)) : Bool :=
    match remaining with

    | [] => true
    | ⟨tk, ek⟩ :: tail =>
        let base_cases := [(1, 2), (1, 3), (2, 3)]
        let recursive := acc.map (fun p => (p.2.i, p.1))
        let all_choices := base_cases ++ recursive

        let is_allowed := all_choices.any (fun (i, j) => i == ek.i && j == ek.j)
        let new_pair : Finset Nat := {ek.i, ek.j}
        let is_distinct := acc.all (fun p => ({p.2.i, p.2.j} : Finset Nat) != new_pair)

        if is_allowed && is_distinct then
          validate tail (⟨tk, ek⟩ :: acc)
        else
          false

  -- Initial call
  if triples.length != n - 3 then false else validate triples []


-- Example for n =6 and n = 7
#eval isValidSequence 6 [
  ⟨4, {
    i := 1, j := 3,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 3
    h_order := by decide, -- 1 < 3
    h_k := by decide      -- 3 < 4
  }⟩,
  ⟨5, {
    i := 1, j := 4,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 4
    h_order := by decide, -- 1 < 4
    h_k := by decide      -- 4 < 5
  }⟩,
  ⟨6, {
    i := 1, j := 5,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 5
    h_order := by decide, -- 1 < 5
    h_k := by decide      -- 5 < 6
  }⟩
]
#eval isValidSequence 7 [
  ⟨4, {
    i := 1, j := 3,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 3
    h_order := by decide, -- 1 < 3
    h_k := by decide      -- 3 < 4
  }⟩,
  ⟨5, {
    i := 1, j := 4,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 4
    h_order := by decide, -- 1 < 4
    h_k := by decide      -- 4 < 5
  }⟩,
  ⟨6, {
    i := 1, j := 5,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 5
    h_order := by decide, -- 1 < 5
    h_k := by decide      -- 5 < 6
  }⟩,
  ⟨7, {
    i := 3, j := 6,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 6
    h_order := by decide, -- 1 < 6
    h_k := by decide      -- 6 < 7
  }⟩
]
instance {k : ℕ} : ToString (Ek k) where
  toString ek := s!"(i: {ek.i}, j: {ek.j})"

def VerifySequence (n : Nat) (triples : List (Σ k : Nat, Ek k)) : Except String Unit :=
  let rec validate (remaining : List (Σ k : Nat, Ek k)) (acc : List (Σ k : Nat, Ek k)) (expected_k : Nat) : Except String Unit :=
    match remaining with


    | [] =>
        if acc.length == n - 3 then .ok ()
        else .error s!"Logic Error: Sequence incomplete. Found {acc.length}, expected {n-3}."

    | ⟨tk, ek⟩ :: tail =>
        if tk != expected_k then
          .error s!"Index Error: Expected k={expected_k}, but found k={tk}."
        else
          let base_cases : List (Nat × Nat) := [(1, 2), (1, 3), (2, 3)]
          -- Use flatMap instead of bind
          let recursive : List (Nat × Nat) := acc.flatMap (fun (p : Σ k : Nat, Ek k) =>
            [(p.2.i, p.1), (p.2.j, p.1)]
          )
          let all_choices : List (Nat × Nat) := base_cases ++ recursive

          if ¬all_choices.any (fun (choice : Nat × Nat) => choice.1 == ek.i && choice.2 == ek.j) then
            let choicesStr := all_choices.map (fun (p : Nat × Nat) => s!"({p.1}, {p.2})")
            .error s!"Logic Error at k={tk}: ({ek.i}, {ek.j}) is not allowed.\nValid options were: {choicesStr}"
          else
            let new_pair : Finset Nat := {ek.i, ek.j}
            if acc.any (fun (p : Σ k : Nat, Ek k) => ({p.2.i, p.2.j} : Finset Nat) == new_pair) then
              .error s!"Duplicate Error at k={tk}: The pair ({ek.i}, {ek.j}) was already used."
            else
              validate tail (⟨tk, ek⟩ :: acc) (expected_k + 1)

  if h : n < 3 then
    if triples.isEmpty then .ok () else .error "n < 3 but list is not empty"
  else if triples.length != n - 3 then
    .error s!"Length Error: List has {triples.length} items, but n={n} requires {n-3}."
  else
    validate triples [] 4





-- Example usage for n = 6 and n = 7
#eval VerifySequence 6 [
  ⟨4, {
    i := 1, j := 3,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 3
    h_order := by decide, -- 1 < 3
    h_k := by decide      -- 3 < 4
  }⟩,
  ⟨5, {
    i := 1, j := 4,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 4
    h_order := by decide, -- 1 < 4
    h_k := by decide      -- 4 < 5
  }⟩,
  ⟨6, {
    i := 1, j := 5,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 5
    h_order := by decide, -- 1 < 5
    h_k := by decide      -- 5 < 6
  }⟩
]
#eval VerifySequence 7 [
  ⟨4, {
    i := 1, j := 3,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 3
    h_order := by decide, -- 1 < 3
    h_k := by decide      -- 3 < 4
  }⟩,
  ⟨5, {
    i := 1, j := 4,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 4
    h_order := by decide, -- 1 < 4
    h_k := by decide      -- 4 < 5
  }⟩,
  ⟨6, {
    i := 1, j := 5,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 5
    h_order := by decide, -- 1 < 5
    h_k := by decide      -- 5 < 6
  }⟩,
  ⟨7, {
    i := 3, j := 6,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 6
    h_order := by decide, -- 1 < 6
    h_k := by decide      -- 6 < 7
  }⟩
]
#eval VerifySequence 7 [
  ⟨4, {
    i := 1, j := 3,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 3
    h_order := by decide, -- 1 < 3
    h_k := by decide      -- 3 < 4
  }⟩,
  ⟨5, {
    i := 2, j := 3,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 4
    h_order := by decide, -- 1 < 4
    h_k := by decide      -- 4 < 5
  }⟩,
  ⟨6, {
    i := 3, j := 5,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 5
    h_order := by decide, -- 1 < 5
    h_k := by decide      -- 5 < 6
  }⟩,
  ⟨7, {
    i := 3, j := 6,
    h_i := by decide,     -- 1 ≤ 1
    h_j := by decide,     -- 2 ≤ 6
    h_order := by decide, -- 1 < 6
    h_k := by decide      -- 6 < 7
  }⟩
]
