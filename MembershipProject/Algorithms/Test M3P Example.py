#!/usr/bin/env python3
"""
Test M3P algorithm with example X to check if X ∈ conv(Pedigrees_6)

Given X:
  x(1,2,3) = 1
  x(1,3,4) = 3/4
  x(2,3,4) = 1/4
  x(1,2,5) = 1/2
  x(3,4,5) = 1/2
  x(1,3,6) = 1/4
  x(1,4,6) = 1/4
  x(2,3,6) = 1/4
  x(2,4,6) = 1/4
"""

from fractions import Fraction
import sys

# Define X as a sparse dictionary
X = {
    (1, 2, 3): Fraction(1, 1),
    (1, 3, 4): Fraction(3, 4),
    (2, 3, 4): Fraction(1, 4),
    (1, 2, 5): Fraction(1, 2),
    (3, 4, 5): Fraction(1, 2),
    (1, 3, 6): Fraction(1, 4),
    (1, 4, 6): Fraction(1, 4),
    (2, 3, 6): Fraction(1, 4),
    (2, 4, 6): Fraction(1, 4),
}

def get_mir_value(x_dict, i, j, k):
    """Get MIR value x(i,j,k)"""
    return x_dict.get((i, j, k), Fraction(0))

def nodes_in_layer(k):
    """Get all nodes (i,j,k) in layer k"""
    if k < 3:
        return []
    nodes = []
    for i in range(1, k):
        for j in range(i+1, k):
            nodes.append((i, j, k))
    return nodes

def is_permitted_arc_45(src_node, tgt_node):
    """Check if arc from layer 4 to layer 5 is permitted (F₄ rules)"""
    i, j, k = src_node
    ip, jp, kp = tgt_node
    
    if k != 4 or kp != 5:
        return False
    
    # Rule [a]: (i,j) ≠ (i',j')
    if i == ip and j == jp:
        return False
    
    # Rule [b]: If j' > 3, then i' must be in {i,j}
    if jp > 3:
        return ip == i or ip == j
    
    return True

def construct_f4_network(x_dict):
    """Construct F₄ network and return as edge list"""
    layer4 = nodes_in_layer(4)
    layer5 = nodes_in_layer(5)
    
    print(f"Layer 4 nodes: {layer4}")
    print(f"Layer 5 nodes: {layer5}")
    print()
    
    # Assign vertex IDs
    source_id = 0
    sink_id = 1 + len(layer4) + len(layer5)
    
    layer4_ids = {node: idx + 1 for idx, node in enumerate(layer4)}
    layer5_ids = {node: idx + 1 + len(layer4) for idx, node in enumerate(layer5)}
    
    edges = []
    
    # Source → Layer 4
    print("Source → Layer 4 edges:")
    for node in layer4:
        i, j, k = node
        cap = get_mir_value(x_dict, i, j, k)
        if cap > 0:
            edges.append((source_id, layer4_ids[node], float(cap), f"src→{node}"))
            print(f"  {source_id} → {layer4_ids[node]} (node {node}): capacity = {cap}")
    print()
    
    # Layer 4 → Layer 5 (with arc rules)
    print("Layer 4 → Layer 5 edges (permitted arcs):")
    for src_node in layer4:
        for tgt_node in layer5:
            if is_permitted_arc_45(src_node, tgt_node):
                i, j, k = tgt_node
                cap = get_mir_value(x_dict, i, j, k)
                if cap > 0:
                    edges.append((layer4_ids[src_node], layer5_ids[tgt_node], 
                                float(cap), f"{src_node}→{tgt_node}"))
                    print(f"  {layer4_ids[src_node]} → {layer5_ids[tgt_node]} "
                          f"({src_node}→{tgt_node}): capacity = {cap}")
    print()
    
    # Layer 5 → Sink
    print("Layer 5 → Sink edges:")
    for node in layer5:
        edges.append((layer5_ids[node], sink_id, 1.0, f"{node}→sink"))
        print(f"  {layer5_ids[node]} → {sink_id} (node {node}→sink): capacity = 1.0")
    print()
    
    return edges, source_id, sink_id, len(layer4) + len(layer5) + 2

def check_f4_feasibility(x_dict):
    """Check if F₄ is feasible (max-flow = 1)"""
    print("="*60)
    print("STEP 1b: Analyzing F₄")
    print("="*60)
    print()
    
    edges, source, sink, num_vertices = construct_f4_network(x_dict)
    
    print(f"F₄ network summary:")
    print(f"  Vertices: {num_vertices}")
    print(f"  Edges: {len(edges)}")
    print(f"  Source: {source}")
    print(f"  Sink: {sink}")
    print()
    
    print("Expected max-flow: 1.0")
    print()
    print("TODO: Call GraphInterface.computeMaxFlow() to compute actual max-flow")
    print("      If max-flow = 1.0, then F₄ is feasible → proceed to extract R₄")
    print("      If max-flow ≠ 1.0, then STOP (X ∉ convex hull)")
    print()
    
    return edges, source, sink, num_vertices

def main():
    print("Testing M3P Algorithm")
    print("="*60)
    print()
    
    print("Given X:")
    for (i, j, k), val in sorted(X.items()):
        print(f"  x({i},{j},{k}) = {val}")
    print()
    
    print("Target: Check if X ∈ conv(Pedigrees_6)")
    print()
    
    # Step 1a: Check P_MI (would use existing feasibility check)
    print("="*60)
    print("STEP 1a: Check P_MI membership")
    print("="*60)
    print("TODO: Run checkFeasibilityDetailed(6, X)")
    print("      Assuming this passes...")
    print()
    
    # Step 1b: Analyze F₄
    edges, source, sink, num_vertices = check_f4_feasibility(X)
    
    print()
    print("="*60)
    print("Next Steps:")
    print("="*60)
    print("1. Integrate with GraphInterface to compute max-flow in F₄")
    print("2. If feasible, compute frozen flows to extract R₄")
    print("3. Update N₄ by subtracting rigid flows")
    print("4. Continue to F₅ and beyond until:")
    print("   - Z_max = 0 (all rigid) → SUCCESS")
    print("   - Max-flow ≠ 1 in some F_k → FAILURE")

if __name__ == "__main__":
    main()