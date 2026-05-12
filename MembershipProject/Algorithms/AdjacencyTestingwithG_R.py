"""
Pedigree Polytope Adjacency Algorithm with Graph Visualization
==============================================================
Implementation of Theorem 4.18 from Chapter 4:
Two pedigrees are adjacent in conv(P_n) iff G_R (graph of rigidity) is connected.

This version includes graph drawing using NetworkX.
"""

import networkx as nx
import matplotlib.pyplot as plt
from collections import deque
from typing import List, Tuple, Set, Optional

# Type aliases
Triple = Tuple[int, int, int]  # (i, j, k) with 1 ≤ i < j < k
Edge = Tuple[int, int]         # (i, j)


# ============================================================================
# GENERATOR FUNCTIONS
# ============================================================================

def edge_of_triple(t: Triple) -> Edge:
    """Extract the edge (i, j) from a triple (i, j, k)."""
    return (t[0], t[1])


def generators(t: Triple) -> Set[Triple]:
    """
    Return the set of all possible generator triples for a given triple.
    
    For t = (a, b, k):
    - If (a,b) = (1,2): no generators (base triple)
    - If b > 3: generators are (r, a, b) for r < a, and (a, s, b) for a < s < b
    - If b ≤ 3 and (a,b) ≠ (1,2): generator is (1,2,3)
    """
    a, b, k = t
    if a == 1 and b == 2:
        return set()
    if b > 3:
        gen = set()
        # Form 1: (r, a, b) for 1 ≤ r < a
        for r in range(1, a):
            gen.add((r, a, b))
        # Form 2: (a, s, b) for a < s < b
        for s in range(a + 1, b):
            gen.add((a, s, b))
        return gen
    else:
        # b ≤ 3 and (a,b) ≠ (1,2) → generator is (1,2,3)
        return {(1, 2, 3)}


# ============================================================================
# PEDIGREE VALIDATION
# ============================================================================

def is_valid_pedigree(triples: List[Triple], n: int, verbose: bool = False) -> bool:
    """Validate that a list of triples forms a valid pedigree of size n."""
    if len(triples) != n - 2:
        if verbose:
            print(f"  Error: expected {n-2} triples, got {len(triples)}")
        return False
    
    if triples[0] != (1, 2, 3):
        if verbose:
            print("  Error: base triple not (1,2,3)")
        return False
    
    edges_seen = set()
    for idx, (a, b, k) in enumerate(triples):
        if k != idx + 3:
            if verbose:
                print(f"  Error: at index {idx}, expected k={idx+3}, got {k}")
            return False
        if not (1 <= a < b < k):
            if verbose:
                print(f"  Error: triple {(a,b,k)} invalid: {1 <= a < b < k} failed")
            return False
        if k >= 4:
            edge = (a, b)
            if edge in edges_seen:
                if verbose:
                    print(f"  Error: duplicate edge {edge} at k={k}")
                return False
            edges_seen.add(edge)
    
    # Check generator property
    for idx, (a, b, k) in enumerate(triples):
        if k <= 3:
            continue
        if b > 3:
            if b > n:
                if verbose:
                    print(f"  Error: generator layer {b} > n")
                return False
            gen_idx = b - 3
            if gen_idx >= idx:
                if verbose:
                    print(f"  Error: generator at layer {b} appears after {k}")
                return False
            gen_triple = triples[gen_idx]
            if gen_triple not in generators((a, b, k)):
                if verbose:
                    print(f"  Error: {gen_triple} is not a generator of {(a,b,k)}")
                return False
        else:
            if triples[0] != (1, 2, 3):
                if verbose:
                    print("  Error: generator should be (1,2,3) but base triple is missing")
                return False
    
    return True


# ============================================================================
# GRAPH OF RIGIDITY G_R
# ============================================================================

def build_rigidity_graph(P: List[Triple], Q: List[Triple], n: int,
                         verbose: bool = True) -> Tuple[Set[Tuple[int, int]], List[int]]:
    """
    Build the graph of rigidity G_R for two pedigrees P and Q.
    
    Returns:
        edges: set of undirected edges (s, q) with s < q
        discords: list of discord layers
    """
    # Validate inputs
    if not is_valid_pedigree(P, n):
        raise ValueError("P is not a valid pedigree")
    if not is_valid_pedigree(Q, n):
        raise ValueError("Q is not a valid pedigree")
    
    # Step 1: Find discords
    discords = []
    for k in range(3, n + 1):
        idx = k - 3
        if P[idx] != Q[idx]:
            discords.append(k)
    
    if verbose:
        print(f"  Discords: {discords}")
    
    if len(discords) <= 1:
        return set(), discords
    
    discord_set = set(discords)
    edges = set()
    
    # Step 2: Process discords from largest to smallest
    for q in sorted(discords, reverse=True):
        q_idx = q - 3
        
        for i in (0, 1):
            t = P[q_idx] if i == 0 else Q[q_idx]
            a, b, _ = t
            other = Q if i == 0 else P
            
            # Condition 2: edge already appears in other at earlier discord
            found = False
            for s in discords:
                if s >= q:
                    continue
                s_idx = s - 3
                if edge_of_triple(other[s_idx]) == (a, b):
                    edges.add((min(q, s), max(q, s)))
                    if verbose:
                        print(f"    Edge added (Condition 2): {min(q,s)}-{max(q,s)} from q={q}, i={i}")
                    found = True
                    break
            
            if found:
                continue
            
            # Condition 1: generator missing
            if b <= 3:
                continue
            
            gen_layer = b
            if gen_layer not in discord_set:
                continue
            
            other_triple = other[gen_layer - 3]
            if other_triple not in generators(t):
                edges.add((min(q, gen_layer), max(q, gen_layer)))
                if verbose:
                    print(f"    Edge added (Condition 1): {min(q,gen_layer)}-{max(q,gen_layer)} from q={q}, i={i}")
    
    return edges, discords


def get_graph(P: List[Triple], Q: List[Triple], n: int) -> nx.Graph:
    """Return a NetworkX graph object representing G_R."""
    edges, discords = build_rigidity_graph(P, Q, n, verbose=False)
    
    G = nx.Graph()
    # Add nodes (discords)
    G.add_nodes_from(discords)
    # Add edges
    G.add_edges_from(edges)
    
    return G


def is_adjacent(P: List[Triple], Q: List[Triple], n: int,
                verbose: bool = True, draw: bool = False,
                title: str = "Graph of Rigidity G_R") -> bool:
    """
    Determine if two pedigrees P and Q are adjacent in conv(P_n).
    
    Returns:
        True if adjacent, False if nonadjacent
    """
    edges, discords = build_rigidity_graph(P, Q, n, verbose)
    
    if verbose:
        print(f"  G_R edges: {sorted(edges)}")
    
    # |D| = 0 or 1 → adjacent (Lemma 4.13)
    if len(discords) <= 1:
        if verbose:
            print("  |D| ≤ 1 → adjacent (Lemma 4.13)")
        if draw and len(discords) == 1:
            # Draw single node graph
            G = nx.Graph()
            G.add_node(discords[0])
            _draw_graph(G, title, discords)
        return True
    
    # Build adjacency list for BFS
    n_vertices = len(discords)
    discord_index = {k: i for i, k in enumerate(discords)}
    adj = [[] for _ in range(n_vertices)]
    for s, t in edges:
        adj[discord_index[s]].append(discord_index[t])
        adj[discord_index[t]].append(discord_index[s])
    
    # BFS to check connectivity
    visited = [False] * n_vertices
    stack = [0]
    visited[0] = True
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if not visited[v]:
                visited[v] = True
                stack.append(v)
    
    connected = all(visited)
    
    if verbose:
        print(f"  Graph connected: {connected}")
        print(f"  Conclusion: {'adjacent' if connected else 'nonadjacent'}")
    
    # Draw graph if requested
    if draw:
        G = nx.Graph()
        G.add_nodes_from(discords)
        G.add_edges_from(edges)
        _draw_graph(G, title, discords, connected)
    
    return connected


def _draw_graph(G: nx.Graph, title: str, discords: List[int],
                connected: Optional[bool] = None):
    """Draw the graph using matplotlib."""
    plt.figure(figsize=(8, 6))
    
    # Use spring layout for better visualization
    pos = nx.spring_layout(G, seed=42)
    
    # Draw nodes
    nx.draw_networkx_nodes(G, pos, node_color='lightblue', node_size=500)
    
    # Draw edges
    nx.draw_networkx_edges(G, pos, edge_color='gray', width=1.5)
    
    # Draw labels
    nx.draw_networkx_labels(G, pos, font_size=12, font_weight='bold')
    
    # Add title
    full_title = title
    if connected is not None:
        full_title += f"\n{'CONNECTED → ADJACENT' if connected else 'DISCONNECTED → NONADJACENT'}"
    plt.title(full_title, fontsize=14)
    
    plt.axis('off')
    plt.tight_layout()
    plt.show()


# ============================================================================
# TEST EXAMPLES WITH VISUALIZATION
# ============================================================================

def test_example_412(draw: bool = True):
    """Example 4.12 from Chapter 4: Adjacent"""
    print("\n" + "=" * 70)
    print("EXAMPLE 4.12 (adjacent)")
    print("=" * 70)
    print("P: edges (1,2), (2,3), (2,5)")
    print("Q: edges (1,2), (2,4), (2,3)")
    
    P = [(1,2,3), (1,2,4), (2,3,5), (2,5,6)]
    Q = [(1,2,3), (1,2,4), (2,4,5), (2,3,6)]
    n = 6
    
    return is_adjacent(P, Q, n, draw=draw, title="Example 4.12: G_R (Adjacent)")


def test_example_413(draw: bool = True):
    """Example 4.13 from Chapter 4: Nonadjacent"""
    print("\n" + "=" * 70)
    print("EXAMPLE 4.13 (nonadjacent)")
    print("=" * 70)
    print("P: edges (1,3), (2,3), (3,4)")
    print("Q: edges (1,2), (1,4), (1,3)")
    
    P = [(1,2,3), (1,3,4), (2,3,5), (3,4,6)]
    Q = [(1,2,3), (1,2,4), (1,4,5), (1,3,6)]
    n = 6
    
    return is_adjacent(P, Q, n, draw=draw, title="Example 4.13: G_R (Nonadjacent)")


def test_counterexample_48(draw: bool = True):
    """Counterexample 4.8: Adjacent in pedigree, nonadjacent in STSP"""
    print("\n" + "=" * 70)
    print("COUNTEREXAMPLE 4.8")
    print("=" * 70)
    print("Adjacent in pedigree polytope, nonadjacent in STSP")
    print()
    print("P: edges (1,2), (1,3), (2,4), (2,6), (3,5), (1,4), (5,8)")
    print("Q: edges (1,3), (2,3), (3,4), (4,6), (3,5), (1,4), (4,7)")
    
    P = [
        (1,2,3), (1,2,4), (1,3,5), (2,4,6), (2,6,7),
        (3,5,8), (1,4,9), (5,8,10)
    ]
    Q = [
        (1,2,3), (1,3,4), (2,3,5), (3,4,6), (4,6,7),
        (3,5,8), (1,4,9), (4,7,10)
    ]
    n = 10
    
    return is_adjacent(P, Q, n, draw=draw, title="Counterexample 4.8: G_R (Adjacent in Pedigree)")


def test_single_discord(draw: bool = True):
    """Single discord case: Adjacent"""
    print("\n" + "=" * 70)
    print("SINGLE DISCORD (adjacent by Lemma 4.13)")
    print("=" * 70)
    
    P = [(1,2,3), (1,2,4), (2,3,5), (2,5,6)]
    Q = [(1,2,3), (1,2,4), (2,3,5), (2,4,6)]
    n = 6
    
    return is_adjacent(P, Q, n, draw=draw, title="Single Discord: G_R (Adjacent)")


def test_example_415(draw: bool = True):
    """Example 4.15: Nonadjacent with multiple components"""
    print("\n" + "=" * 70)
    print("EXAMPLE 4.15 (nonadjacent with disconnected G_R)")
    print("=" * 70)
    
    P = [(1,2,3), (1,3,4), (2,3,5), (3,4,6)]
    Q = [(1,2,3), (1,2,4), (1,4,5), (1,3,6)]
    n = 6
    
    return is_adjacent(P, Q, n, draw=draw, title="Example 4.15: G_R (Disconnected → Nonadjacent)")


# ============================================================================
# MAIN
# ============================================================================

if __name__ == "__main__":
    print("\n" + "=" * 70)
    print("PEDIGREE POLYTOPE ADJACENCY ALGORITHM")
    print("Based on Chapter 4: Graph of Rigidity Characterization")
    print("=" * 70)
    
    # Run all tests with visualization
    # Set draw=False to disable graph drawing (for batch runs)
    results = {}
    
    results["Example 4.12"] = test_example_412(draw=True)
    results["Example 4.13"] = test_example_413(draw=True)
    results["Single Discord"] = test_single_discord(draw=True)
    results["Counterexample 4.8"] = test_counterexample_48(draw=True)
    results["Example 4.15"] = test_example_415(draw=True)
    
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    for name, result in results.items():
        status = "ADJACENT" if result else "NONADJACENT"
        print(f"{name:25} → {status}")
    
    print("\n" + "=" * 70)
    print("ALGORITHM COMPLEXITY: O(n²)")
    print("Graph visualization shows G_R with nodes = discords, edges = welding relations")
    print("=" * 70)