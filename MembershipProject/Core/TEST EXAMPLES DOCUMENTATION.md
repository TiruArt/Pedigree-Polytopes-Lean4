# M3P Test Examples Documentation (n=6)

## Overview

This document explains the spectrum of test examples for the M3P (Multicommodity Flow for Pedigree Polytope) algorithm with n=6. Each example is designed to fail or succeed at specific stages, helping to understand and test the algorithm's behavior.

## The M3P Algorithm Stages

For a point X ∈ ℝ^(n choose 3), the M3P algorithm checks membership in conv(Pedigrees_n) through these stages:

1. **P_MI(n) Check**: Basic feasibility (non-negativity, supply/demand balance)
2. **F_4 Check**: Single-commodity max-flow from layer 4 → layer 5
3. **F_5 Check**: Single-commodity max-flow from layer 5 → layer 6 (with rigid pedigrees from F_4)
4. **MCF(5) Check**: **Multicommodity flow** - Can all commodities from S_5 route simultaneously?
5. Continue to F_6, MCF(6), etc.

## Understanding MCF(k)

**Key Insight**: While each commodity individually might be "packable" (can route through its restricted network), they might **conflict** when routing simultaneously due to:
- Shared arc capacities
- Shared node capacities
- Restricted network constraints

### What are Commodities?

For each stage l ≥ 5, the commodities S_l are **the arcs in F_l**:
- Each arc a in F_l corresponds to a commodity s (written a ↔ s)
- Each commodity has a demand v_s (flow through its designated arc)
- Each commodity must route through its restricted network N_{l-1}(s)

### MCF(k) Problem

The multicommodity flow problem MCF(k) routes **all** commodities from S_5 ∪ S_6 ∪ ... ∪ S_k simultaneously, subject to:
- Arc capacity constraints: Σ_s f^s_a ≤ c_a
- Node capacity constraints: Σ_s Σ_{incoming arcs} f^s_a ≤ x̄(v)
- Flow conservation at intermediate nodes
- Restriction to permitted arcs for each commodity
- Source availability constraints

**Objective**: Maximize z = Σ_{s ∈ S_k} v^s

---

## Test Examples for n=6

### Dimension of Space
For n=6, we have (6 choose 3) = 20 nodes:
- Layer 3: 1 node: (1,2,3)
- Layer 4: 3 nodes: (1,2,4), (1,3,4), (2,3,4)
- Layer 5: 6 nodes: (1,2,5), (1,3,5), (1,4,5), (2,3,5), (2,4,5), (3,4,5)
- Layer 6: 10 nodes: (1,2,6), ..., (4,5,6)

So X ∈ ℝ^20.

---

## Example 1: Not Feasible for MIR(6) - Negative Values

**File**: `Example1_InfeasibleMIR_Negative.txt`

**Key Features**:
- x(2,3,4) = -0.25 (NEGATIVE!)
- Violates non-negativity constraint

**Expected Behavior**:
- ❌ FAILS at P_MI(6) feasibility check
- Should be caught by `checkParsedDataFeasibility` or during parsing
- Never reaches F_4

**Why It Fails**:
The basic polytope P_MI(n) requires all x(i,j,k) ≥ 0. This is a hard constraint enforced by the SparseEntry type in your Lean code.

---

## Example 1b: Not Feasible for MIR(6) - Supply/Demand Imbalance

**File**: `Example1b_InfeasibleMIR_SupplyDemand.txt`

**Key Features**:
- Layer 4 total: x(1,2,4) + x(1,3,4) + x(2,3,4) = 0.25 + 0.25 + 0 = 0.5
- Layer 5 total: Σ x(·,·,5) = 0.5 + 0.5 + 0.5 + 0.5 = 2.0
- Supply (0.5) << Demand (2.0)

**Expected Behavior**:
- ❌ FAILS at P_MI(6) feasibility check
- Supply-demand imbalance at layers
- Flow conservation violated

**Why It Fails**:
The generation matrix equations require that flow entering layer k+1 equals flow leaving layer k. This example violates that fundamental constraint.

---

## Example 2: Feasible for MIR(6), Not Feasible for F_4

**File**: `Example2_FailsF4.txt`

**Key Features**:
- All capacity concentrated on (2,3,4): x(2,3,4) = 1.0
- Layer 5 has capacity on (1,4,5) which (2,3,4) cannot reach
- Forbidden arc rule: (2,3,4) → (1,4,5) is forbidden because j'=4 > 3 requires i'=1 ∈ {2,3}, which is FALSE

**Expected Behavior**:
- ✓ PASSES P_MI(6)
- ❌ FAILS at F_4 construction/solving
- Max-flow in F_4 < 1.0 (expected flow)

**Why It Fails**:
The forbidden arc rules for F_4 create structural constraints. When all supply is on nodes that cannot reach sufficient demand nodes through permitted arcs, max-flow fails.

**F_4 Forbidden Arc Rules**:
- (i,j,4) → (i',j',5) is forbidden if:
  - [a] (i,j) = (i',j') (no self-loops)
  - [b] If j' > 3, then i' must be in {i,j}

---

## Example 3: Feasible for F_4, Not Feasible for F_5

**File**: `Example3_FailsF5.txt`

**Key Features**:
- F_4 can route flow: (1,2,4) and (1,3,4) each have 0.5 capacity
- Layer 5 reachable: (1,2,5) and (3,4,5) have 0.5 capacity each
- Layer 6 bottleneck: Only (1,2,6) and (4,5,6) have capacity (0.25 each)
- Insufficient capacity in layer 6 for rigid pedigrees to extend

**Expected Behavior**:
- ✓ PASSES P_MI(6)
- ✓ PASSES F_4 (max-flow = 1.0)
- ❌ FAILS at F_5
- After extracting rigid pedigrees R_4, they cannot extend to layer 6 properly

**Why It Fails**:
F_4 succeeds and produces rigid pedigrees. However, F_5 must route these pedigrees (plus any flexible flow from layer 5) to layer 6. The bottleneck at layer 6 prevents this.

**What Happens**:
1. F_4 solves: max-flow = 1.0 ✓
2. Extract R_4 (rigid pedigrees with total flow = some amount)
3. Construct F_5 with virtual sources from R_4
4. F_5 max-flow < expected flow ✗

---

## Example 4: Feasible for F_4 and F_5, Not Feasible for MCF(5)

**File**: `Example4_FailsMCF5.txt`

**Key Features**:
- Layer 4: Balanced distribution (1/3 each)
- Layer 5: Multiple paths with capacity 1/6 each
- Layer 6: Uniform but limited capacity (1/8 each) - BOTTLENECK
- Each commodity individually can route, but they conflict!

**Expected Behavior**:
- ✓ PASSES P_MI(6)
- ✓ PASSES F_4 (max-flow = 1.0)
- ✓ PASSES F_5 (max-flow = expected)
- ❌ FAILS at MCF(5)

**Why It Fails - The MCF Conflict**:

This is the **key example** for understanding MCF!

1. **F_5 solves individually**: When we compute F_5, we're solving a single-commodity max-flow problem. The flow can route through available paths.

2. **Commodities from S_5**: After solving F_5, we have multiple arcs (commodities) in S_5, each with a certain flow v_s.

3. **MCF(5) routes simultaneously**: Now we need to route ALL commodities from S_5 together through the network. They must share:
   - Arc capacities
   - Node capacities (especially at layer 6)

4. **Bottleneck at Layer 6**: Each node in layer 6 has capacity 1/8. Multiple commodities want to route through the same nodes, but the total node capacity is insufficient.

5. **Result**: MCF(5) is infeasible or objective value < expected.

**Analogy**: Think of it like this:
- Individual packability: "Each truck can find a route to the destination"
- MCF: "Can all trucks drive simultaneously without traffic jams?"

Even if each truck individually has a valid route, when they all drive at once, they might create congestion at bottleneck nodes/roads.

---

## Example 5: SUCCESS - Feasible for All Stages (Uniform)

**File**: `Example5_Success_Uniform.txt`

**Key Features**:
- Uniform distribution across all layers
- Layer 4: 1/3 each
- Layer 5: 1/6 each
- Layer 6: 1/10 each
- Well-balanced, no bottlenecks

**Expected Behavior**:
- ✓ PASSES P_MI(6)
- ✓ PASSES F_4
- ✓ PASSES F_5
- ✓ PASSES MCF(5)
- ✓ SUCCESS: X ∈ conv(Pedigrees_6)

**Why It Succeeds**:
The uniform distribution ensures that:
- Flow is balanced across all paths
- No single node/arc becomes a bottleneck
- Commodities can route simultaneously without conflicts
- All capacity constraints are satisfied with slack

---

## Example 5b: SUCCESS - Actual Pedigree Indicator

**File**: `Example5b_Success_Pedigree.txt`

**Key Features**:
- Represents a single pedigree path: (1,2,3) → (1,3,4) → (3,4,5) → (4,5,6)
- All values are 0 or 1 (indicator/characteristic function)
- This is a vertex of conv(Pedigrees_6)

**Expected Behavior**:
- ✓ PASSES all stages
- This is an extreme point of the polytope
- Trivially satisfies all MCF conditions (single path)

**Why It Succeeds**:
Being an actual pedigree (extreme point), it's by definition in conv(Pedigrees_6). All flow follows a single rigid path with no flexibility, so there are no conflicts.

---

## Testing Strategy

### Phase 1: Unit Tests
1. Test Example 1 & 1b → Should fail at parsing or P_MI check
2. Test Example 2 → Should fail at F_4 with specific error about max-flow < 1

### Phase 2: F_4 and F_5 Tests
3. Test Example 3 → Should pass F_4, fail at F_5
4. Verify rigid pedigree extraction from F_4 works correctly

### Phase 3: MCF Implementation
5. Implement MCF(5) solver (LP formulation)
6. Test Example 4 → Should pass F_4 & F_5, fail at MCF(5)
7. This is the critical test for MCF implementation!

### Phase 4: Success Cases
8. Test Example 5 → Should pass all stages
9. Test Example 5b → Should pass all stages (vertex case)

---

## MCF Implementation Notes

### Data Needed for MCF(k)

```lean
structure MCFInput (k : ℕ) where
  -- All commodities from stages 5 through k
  commodities : List Commodity  -- Each has source, sink, demand v_s
  
  -- Restricted network for each commodity
  restrictedNetworks : Commodity → FlowNetwork
  
  -- Arc capacities
  arcCapacities : (Node × Node) → Rat
  
  -- Node capacities
  nodeCapacities : Node → Rat
  
  -- Availability at rigid pedigree sources
  rigidAvailabilities : List (PedigreePath × Rat)
```

### LP Formulation

Variables:
- f^s_a ≥ 0 for each commodity s, arc a

Constraints:
1. Arc capacity: Σ_s f^s_a ≤ c_a for all arcs a
2. Node capacity: Σ_s Σ_{incoming} f^s_a ≤ x̄(v) for all nodes v
3. Flow conservation: Σ_{in} f^s_a = Σ_{out} f^s_a for intermediate nodes
4. Restricted arcs: f^s_a > 0 only if a ∈ N_{l-1}(s)
5. Commodity demand: Σ_{entering designated arc} f^s_a = v_s

Objective:
- Maximize z = Σ_{s ∈ S_k} v^s

### Python Implementation

Use `pulp` or `scipy.optimize.linprog` to solve the LP.

---

## Conclusion

These examples provide a complete spectrum of test cases for the M3P algorithm:

1. **Examples 1 & 1b**: Test basic feasibility (P_MI)
2. **Example 2**: Test F_4 with forbidden arc constraints
3. **Example 3**: Test F_5 with rigid pedigree extension
4. **Example 4**: **Test MCF(5) - the key multicommodity flow challenge**
5. **Examples 5 & 5b**: Verify success cases work correctly

The progression helps debug each stage incrementally and understand where and why the algorithm might fail.