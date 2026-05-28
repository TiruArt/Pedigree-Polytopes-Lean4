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
-- 2. THE REWORKED LOOP-BASED VALID TREE VALIDATOR
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
-- 3. VALID RANDOM TREE GENERATOR (SAFE MATCH LOOKUPS)
-- ==================================================================

def getValidCandidates {n : Nat} (k : Nat) (_h_k : k ≤ n) (currentTree : List (Node n)) : List (Node n) :=
  Id.run do
    let mut candidates : List (Node n) := []
    for j in [2 : k] do
      for i in [1 : j] do
        if h_bound : 1 ≤ i ∧ i < j ∧ j < k ∧ k ≤ n then
          let candidateNode : Node n := ⟨i, j, k, h_bound⟩
          let hasParent := currentTree.any (fun p => decideIsParent p candidateNode)
          let noClash := currentTree.all (fun old => old.i != i || old.j != j)
          if hasParent && noClash then
            candidates := candidates ++ [candidateNode]
    return candidates

def generateRandomValidTree (n : Nat) (h_n : 3 ≤ n) : IO (List (Node n)) := do
  have h_default : 1 ≤ 1 ∧ 1 < 2 ∧ 2 < 3 ∧ 3 ≤ n := by omega
  let defaultNode : Node n := ⟨1, 2, 3, h_default⟩

  let rec loop (fuel : Nat) (k : Nat) (acc : List (Node n)) : IO (Option (List (Node n))) := do
    match fuel with


    | 0 => return none
    | fuel + 1 =>
      if k > n then
        return some acc
      else
        if h_k : k ≤ n then
          let options := getValidCandidates k h_k acc
          if options.isEmpty then
            return none
          else
            let idx ← IO.rand 0 (options.length - 1)
            let chosen := options.getD idx defaultNode
            match ← loop fuel (k + 1) (acc ++ [chosen]) with


            | some finalTree => return some finalTree
            | none => loop fuel k acc
        else
          return none

  let root : Node n := node 1, 2, 3
  match ← loop 500 4 [root] with


  | some t => return t
  | none => return [root]


-- ==================================================================
-- 4. GRAPH DEPENDENCY COMPONENT HELPERS
-- ==================================================================

def getComponentClosure (edges : List (Nat × Nat)) (current : List Nat) : List Nat :=
  let rec trace (fuel : Nat) (visited : List Nat) : List Nat :=
    match fuel with


    | 0 => visited
    | fuel + 1 =>
      let nextNeighbors := edges.filterMap fun (u, v) =>
        if visited.contains u && !visited.contains v then some v
        else if visited.contains v && !visited.contains u then some u
        else none
      if nextNeighbors.isEmpty then visited
      else trace fuel (visited ++ nextNeighbors |>.eraseDups)
  trace edges.length current.eraseDups


-- ==================================================================
-- 5. UPGRADED VISUAL GRAPH PROPAGATION ADJACENCY CHECKER
-- ==================================================================

/--
Checks adjacency by building a dependency graph.
Now runs in IO so it can print the vertices D and the discovered edges.
-/
def areTreesAdjacentDependencyGraph (n : Nat) (h_n : 3 ≤ n) (T1 T2 : List (Node n)) : IO Bool := do
  if T1 == T2 then return false

  -- 1. Identify the differing levels D (Vertices of our dependency graph)
  let D := (List.range (n + 1)).filter fun l =>
    let choice1 := T1.find? (fun t => t.k == l)
    let choice2 := T2.find? (fun t => t.k == l)
    choice1 != choice2

  if D.length == 0 then return false
  if D.length == 1 then return true

  let mut edges : List (Nat × Nat) := []

  -- We loop downwards from k = n down to 4
  for k_idx in [0 : n - 3] do
    let k := n - k_idx
    if D.contains k then
      match T1.find? (fun t => t.k == k), T2.find? (fun t => t.k == k) with


      | some _t1_k, some t2_k =>

        for l in D do
          if l != k then
            match T1.find? (fun t => t.k == l), T2.find? (fun t => t.k == l) with
            | some t1_l, some t2_l =>

              -- CHECK 1: PARENT AVAILABILITY (TWO-WAY)
              if l < k && decideIsParent t2_l t2_k && !decideIsParent t1_l t2_k then
                edges := edges ++ [(k, l)]
              if l < k && decideIsParent t1_l _t1_k && !decideIsParent t2_l _t1_k then
                edges := edges ++ [(k, l)]

              -- CHECK 2: FOOTPRINT CLASHES (TWO-WAY)
              if t2_k.i == t1_l.i && t2_k.j == t1_l.j then
                edges := edges ++ [(k, l)]
              if _t1_k.i == t2_l.i && _t1_k.j == t2_l.j then
                edges := edges ++ [(k, l)]



            | _, _ => pure ()
      | _, _ => pure ()

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
          -- Print out the graph state right when we hit a non-adjacency proof
          IO.println s!"  -> [Graph Trace] Vertices D: {D}"
          IO.println s!"  -> [Graph Trace] Edges Found: {edges}"
          IO.println s!"  -> [Graph Trace] Breaking proper sub-component C_{k}: {C}"
          return false

  -- If we looped all the way through, print the full graph built before returning true
  IO.println s!"  -> [Graph Trace] Vertices D: {D}"
  IO.println s!"  -> [Graph Trace] Edges Found: {edges}"
  return true


-- ==================================================================
-- 6. UNIFIED TESTING HARNESS FOR RANDOM TREES (WITH VISUAL DETAILS)
-- ==================================================================

def printTreeSummary {n : Nat} (tree : List (Node n)) : String :=
  let nodeStrings := tree.map fun t => s!"\{{t.i}, {t.j}, {t.k}}"
  s!"[{String.intercalate ", " nodeStrings}]"

def evaluateRandomPairs (n : Nat) (h_n : 3 ≤ n) (pairCount : Nat) : IO Unit := do
  IO.println s!"\n===================================================="
  IO.println s!"SIMULATING {pairCount} RANDOM VERTEX PAIRS FOR n = {n}"
  IO.println "===================================================="

  for idx in [1 : pairCount + 1] do
    let treeA ← generateRandomValidTree n h_n
    let treeB ← generateRandomValidTree n h_n

    let vA := decideTree n h_n treeA
    let vB := decideTree n h_n treeB

    IO.println s!"\n[Pair #{idx}]"
    if vA && vB then
      IO.println s!"  -> Tree 1: {printTreeSummary treeA}"
      IO.println s!"  -> Tree 2: {printTreeSummary treeB}"

      -- Execute the printing checker
      let adj ← areTreesAdjacentDependencyGraph n h_n treeA treeB
      IO.println s!"  -> ARE THEY ADJACENT? * {adj} *"
    else
      IO.println s!"  -> Skipping (Failed to locate a valid random pair boundary)"

def runUnifiedPipeline : IO Unit := do
  IO.println "--- STARTING VISUAL RANDOM POLYTOPE STRESS TESTS ---"

  have h6 : 3 ≤ 6 := by omega
  evaluateRandomPairs 6 h6 2

  have h7 : 3 ≤ 7 := by omega
  evaluateRandomPairs 7 h7 2

#eval! runUnifiedPipeline
