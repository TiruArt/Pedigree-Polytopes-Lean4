"""
Pedigree Polytope Adjacency Algorithm
======================================
No external dependencies required.
"""

from collections import deque
from typing import List, Tuple, Set


# ============================================================================
# GENERATOR FUNCTIONS
# ============================================================================

def edge_of_triple(t):
    return (t[0], t[1])


def generators(t):
    a, b, k = t
    if a == 1 and b == 2:
        return set()
    if b > 3:
        gen = set()
        for r in range(1, a):
            gen.add((r, a, b))
        for s in range(a + 1, b):
            gen.add((a, s, b))
        return gen
    else:
        return {(1, 2, 3)}


# ============================================================================
# PEDIGREE VALIDATION
# ============================================================================

def is_valid_pedigree(triples, n, verbose=False):
    if len(triples) != n - 2:
        return False
    if triples[0] != (1, 2, 3):
        return False
    edges_seen = set()
    for idx, (a, b, k) in enumerate(triples):
        if k != idx + 3:
            return False
        if not (1 <= a < b < k):
            return False
        if k >= 4:
            edge = (a, b)
            if edge in edges_seen:
                return False
            edges_seen.add(edge)
    for idx, (a, b, k) in enumerate(triples):
        if k <= 3:
            continue
        if b > 3:
            if b > n:
                return False
            gen_idx = b - 3
            if gen_idx >= idx:
                return False
            gen_triple = triples[gen_idx]
            if gen_triple not in generators((a, b, k)):
                return False
        else:
            if triples[0] != (1, 2, 3):
                return False
    return True


# ============================================================================
# GRAPH OF RIGIDITY G_R
# ============================================================================

def build_rigidity_graph(P, Q, n, verbose=True):
    if not is_valid_pedigree(P, n):
        raise ValueError("P is not a valid pedigree")
    if not is_valid_pedigree(Q, n):
        raise ValueError("Q is not a valid pedigree")
    
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
    
    for q in sorted(discords, reverse=True):
        q_idx = q - 3
        
        for i in (0, 1):
            t = P[q_idx] if i == 0 else Q[q_idx]
            a, b, _ = t
            other = Q if i == 0 else P
            
            found = False
            for s in discords:
                if s >= q:
                    continue
                s_idx = s - 3
                if edge_of_triple(other[s_idx]) == (a, b):
                    edges.add((min(q, s), max(q, s)))
                    if verbose:
                        print(f"    Edge added (Condition 2): {min(q,s)}-{max(q,s)} from q={q}")
                    found = True
                    break
            
            if found:
                continue
            
            if b <= 3:
                continue
            
            gen_layer = b
            if gen_layer not in discord_set:
                continue
            
            other_triple = other[gen_layer - 3]
            if other_triple not in generators(t):
                edges.add((min(q, gen_layer), max(q, gen_layer)))
                if verbose:
                    print(f"    Edge added (Condition 1): {min(q,gen_layer)}-{max(q,gen_layer)} from q={q}")
    
    return edges, discords


def draw_ascii_graph(discords, edges):
    """Draw a simple ASCII representation of the graph."""
    if not discords:
        print("  (no discords)")
        return
    
    print("\n  " + "=" * 50)
    print("  Graph of Rigidity G_R")
    print("  " + "=" * 50)
    
    # Create adjacency dictionary
    adj = {d: [] for d in discords}
    for s, t in edges:
        adj[s].append(t)
        adj[t].append(s)
    
    # Sort for consistent output
    discords_sorted = sorted(discords)
    
    # Print adjacency list
    print("\n  Adjacency List:")
    for d in discords_sorted:
        neighbors = sorted(adj[d])
        if neighbors:
            print(f"    {d} → {neighbors}")
        else:
            print(f"    {d} → (isolated)")
    
    # Draw graph structure
    if len(discords) <= 8:
        node_map = {d: chr(ord('A') + i) for i, d in enumerate(discords_sorted)}
        print("\n  Node Mapping:")
        for d, letter in node_map.items():
            print(f"    {d} → {letter}")
        
        print("\n  Graph Structure:")
        for s, t in sorted(edges):
            print(f"    {node_map[s]} -- {node_map[t]}")
    
    # Check connectivity
    if len(discords) > 0:
        visited = set()
        stack = [discords_sorted[0]]
        while stack:
            u = stack.pop()
            if u in visited:
                continue
            visited.add(u)
            for v in adj[u]:
                if v not in visited:
                    stack.append(v)
        
        print(f"\n  Connectivity: {'CONNECTED' if len(visited) == len(discords) else 'DISCONNECTED'}")
        if len(visited) != len(discords):
            remaining = set(discords) - visited
            print(f"    Component 1: {sorted(visited)}")
            print(f"    Remaining nodes: {sorted(remaining)}")


def is_adjacent(P, Q, n, verbose=True):
    edges, discords = build_rigidity_graph(P, Q, n, verbose)
    
    if verbose:
        print(f"\n  G_R Edges: {sorted(edges)}")
        draw_ascii_graph(discords, edges)
    
    if len(discords) <= 1:
        if verbose:
            print("\n  |D| ≤ 1 → ADJACENT (Lemma 4.13)")
        return True
    
    # Build adjacency list for BFS
    n_vertices = len(discords)
    discord_index = {k: i for i, k in enumerate(discords)}
    adj = [[] for _ in range(n_vertices)]
    for s, t in edges:
        adj[discord_index[s]].append(discord_index[t])
        adj[discord_index[t]].append(discord_index[s])
    
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
        print(f"\n  Result: {'ADJACENT' if connected else 'NONADJACENT'}")
        print(f"  (Graph is {'connected' if connected else 'disconnected'})")
    
    return connected


# ============================================================================
# TEST EXAMPLES
# ============================================================================

def test_example_412():
    print("\n" + "=" * 70)
    print("EXAMPLE 4.12 (adjacent)")
    print("=" * 70)
    print("P: edges (1,2), (2,3), (2,5)")
    print("Q: edges (1,2), (2,4), (2,3)")
    
    P = [(1,2,3), (1,2,4), (2,3,5), (2,5,6)]
    Q = [(1,2,3), (1,2,4), (2,4,5), (2,3,6)]
    n = 6
    
    return is_adjacent(P, Q, n)


def test_example_413():
    print("\n" + "=" * 70)
    print("EXAMPLE 4.13 (nonadjacent)")
    print("=" * 70)
    print("P: edges (1,3), (2,3), (3,4)")
    print("Q: edges (1,2), (1,4), (1,3)")
    
    P = [(1,2,3), (1,3,4), (2,3,5), (3,4,6)]
    Q = [(1,2,3), (1,2,4), (1,4,5), (1,3,6)]
    n = 6
    
    return is_adjacent(P, Q, n)


def test_single_discord():
    print("\n" + "=" * 70)
    print("SINGLE DISCORD (adjacent by Lemma 4.13)")
    print("=" * 70)
    
    P = [(1,2,3), (1,2,4), (2,3,5), (2,5,6)]
    Q = [(1,2,3), (1,2,4), (2,3,5), (2,4,6)]
    n = 6
    
    return is_adjacent(P, Q, n)


def test_counterexample_48():
    print("\n" + "=" * 70)
    print("COUNTEREXAMPLE 4.8 (adjacent in pedigree, nonadjacent in STSP)")
    print("=" * 70)
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
    
    return is_adjacent(P, Q, n)


def test_example_415():
    print("\n" + "=" * 70)
    print("EXAMPLE 4.15 (nonadjacent, disconnected G_R)")
    print("=" * 70)
    
    P = [(1,2,3), (1,3,4), (2,3,5), (3,4,6)]
    Q = [(1,2,3), (1,2,4), (1,4,5), (1,3,6)]
    n = 6
    
    return is_adjacent(P, Q, n)


# ============================================================================
# MAIN
# ============================================================================

if __name__ == "__main__":
    print("\n" + "=" * 70)
    print("PEDIGREE POLYTOPE ADJACENCY ALGORITHM")
    print("Based on Chapter 4: Graph of Rigidity Characterization")
    print("=" * 70)
    
    results = {}
    results["Example 4.12"] = test_example_412()
    results["Example 4.13"] = test_example_413()
    results["Single Discord"] = test_single_discord()
    results["Counterexample 4.8"] = test_counterexample_48()
    results["Example 4.15"] = test_example_415()
    
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    for name, result in results.items():
        status = "ADJACENT" if result else "NONADJACENT"
        print(f"{name:25} → {status}")
    
    print("\n" + "=" * 70)
    print("ALGORITHM COMPLEXITY: O(n²)")
    print("=" * 70)