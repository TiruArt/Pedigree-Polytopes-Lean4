import Mathlib.Tactic

-- ==================================================================
-- 1. BASE SYSTEM TYPES (WITH MANDATORY BOUNDS HYPOTHESIS)
-- ==================================================================

structure Node (n : Nat) where
  i : Nat
  j : Nat
  k : Nat
  h_bound : 1 ≤ i ∧ i < j ∧ j < k ∧ k ≤ n
deriving BEq, DecidableEq, Repr

macro "node" i:term "," j:term "," k:term : term =>
  `(Node.mk $i $j $k (by omega))


-- ==================================================================
-- 2. THE LOOP-BASED VALID TREE VALIDATOR
-- ==================================================================

def decideIsParent {n : Nat} (t' t : Node n) : Bool :=
  (t'.k == Max.max 3 t.j) &&
  (t'.i == t.i || t'.j == t.i || t'.k == t.i) &&
  (t'.i == t.j || t'.j == t.j || t'.k == t.j)

def decideTree (n : Nat) (h_n : 3 ≤ n) (nodes : List (Node n)) : Bool :=
  let hasRoot := nodes.contains (Node.mk 1 2 3 (by omega))
  let validBounds := nodes.all fun t => 1 ≤ t.i && t.i < t.j && t.j < t.k && t.k ≤ n
  let rangeK := (List.range (n + 1)).filter (· ≥ 3)
  let exactKCount := rangeK.all fun targetK => (nodes.filter (fun t => t.k == targetK)).length == 1
  let validParents := nodes.all fun t => if t.k ≤ 3 then true else nodes.any fun p => decideIsParent p t
  let uniqueFootprints := nodes.all fun t1 => (nodes.filter (fun t2 => t1.i == t2.i && t1.j == t2.j)).length == 1
  hasRoot && validBounds && exactKCount && validParents && uniqueFootprints


-- ==================================================================
-- 3. GRAPH DEPENDENCY COMPONENT HELPERS
-- ==================================================================

def getComponentClosure (edges : List (Nat × Nat)) (current : List Nat) : List Nat :=
  let rec trace (fuel : Nat) (visited : List Nat) : List Nat :=
    match fuel with

    | 0 => visited
    | fuel + 1 =>
      -- Find all nodes where 'u' is visited and 'v' is not yet visited
      let nextNeighbors := edges.filterMap fun (u, v) =>
        if visited.contains u && !visited.contains v then some v else none

      -- If no new neighbors are found, we have reached the fixpoint
      if nextNeighbors.isEmpty then
        visited
      else
        -- Merge the unique new neighbors into the visited list and recurse
        let newVisited := visited ++ nextNeighbors.filter (!visited.contains ·)
        trace fuel newVisited

  trace edges.length current

-- ==================================================================
-- 4. REWORKED TWO-WAY DEPENDENCY GRAPH ADJACENCY CHECKER
-- ==================================================================

def areTreesAdjacentDependencyGraph (n : Nat) (h_n : 3 ≤ n) (T1 T2 : List (Node n)) : Bool :=
  if T1 == T2 then false else

  let D := (List.range (n + 1)).filter fun l =>
    let choice1 := T1.find? (fun t => t.k == l)
    let choice2 := T2.find? (fun t => t.k == l)
    choice1 != choice2

  if D.length == 0 then false else
  if D.length == 1 then true else

  Id.run do
    let mut edges : List (Nat × Nat) := []

    for k_idx in [0 : n - 3] do
      let k := n - k_idx
      if D.contains k then
        match T1.find? (fun t => t.k == k), T2.find? (fun t => t.k == k) with

        | some t1_k, some t2_k =>

          -- We iterate through all other differing levels l to log dependencies
          for l in D do
            if l != k then
              match T1.find? (fun t => t.k == l), T2.find? (fun t => t.k == l) with
              | some t1_l, some t2_l =>

                -- --- CHECK 1: PARENT AVAILABILITY (TWO-WAY) ---
                -- Direction A: T2 node needs level l from T2, but T1 leaves it stranded
                if l < k && decideIsParent t2_l t2_k && !decideIsParent t1_l t2_k then
                  edges := edges ++ [(k, l)]
                -- Direction B: T1 node needs level l from T1, but swapping to T2 leaves it stranded
                if l < k && decideIsParent t1_l t1_k && !decideIsParent t2_l t1_k then
                  edges := edges ++ [(k, l)]

                -- --- CHECK 2: FOOTPRINT CLASHES (TWO-WAY) ---
                -- Direction A: T2 node's footprint clashes with an active node from T1
                if t2_k.i == t1_l.i && t2_k.j == t1_l.j then
                  edges := edges ++ [(k, l)]
                -- Direction B: T1 node's footprint clashes with an incoming node from T2
                if t1_k.i == t2_l.i && t1_k.j == t2_l.j then
                  edges := edges ++ [(k, l)]


              | _, _ => pure ()
        | _, _ => pure ()

        -- Clean up and closure tracking
        edges := edges.eraseDups
        let C := getComponentClosure edges [k] |>.filter (D.contains ·)

        -- Evaluate stop condition
        if C.length > 0 && C.length < D.length then
          let R := T1.map fun t1 =>
            if C.contains t1.k then
              match T2.find? (fun t2 => t2.k == t1.k) with

              | some t2 => t2
              | none => t1
            else t1

          if decideTree n h_n R then
            return false

    return true


-- ==================================================================
-- 5. RUNTIME VALIDATION ENVIRONMENT WITH THE SIDE-BY-SIDE SHOWN TREES
-- ==================================================================

def runGraphPipeline : IO Unit := do
  let n := 6
  have h6 : 3 ≤ 6 := by omega

  IO.println "--- LEAN 4 VERIFICATION ENVIRONMENT (TWO-WAY GRAPH) ---"

  let r : Node n := node 1, 2, 3

  -- Tree 1 Setup: The Left-Leaning Chain
  let t4A : Node n := node 1, 3, 4
  let t5A : Node n := node 1, 4, 5
  let t6A : Node n := node 1, 5, 6
  let tree1 : List (Node n) := [r, t4A, t5A, t6A]

  -- Tree 2 Setup: The Right-Leaning Chain
  let t4B : Node n := node 2, 3, 4
  let t5B : Node n := node 2, 4, 5
  let t6B : Node n := node 2, 5, 6
  let tree2 : List (Node n) := [r, t4B, t5B, t6B]

  IO.println s!"Is tree1 valid? {decideTree n h6 tree1}"
  IO.println s!"Is tree2 valid? {decideTree n h6 tree2}"

  let adjacent := areTreesAdjacentDependencyGraph n h6 tree1 tree2
  IO.println s!"\nAre tree1 and tree2 adjacent under the two-way propagation algorithm? {adjacent}"

#eval! runGraphPipeline
