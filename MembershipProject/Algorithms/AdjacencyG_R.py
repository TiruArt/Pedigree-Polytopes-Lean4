"""
Pedigree Polytope Adjacency Algorithm with NetworkX Visualization
"""

import networkx as nx
import matplotlib.pyplot as plt
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


def draw_graph(P, Q, n, title="Graph of Rigidity G_R"):
    """Draw G_R using matplotlib"""
    edges, discords = build_rigidity_graph(P, Q, n, verbose=False)
    
    if len(discords) == 0:
        print("No discords → P = Q (trivially adjacent)")
        return
    
    G = nx.Graph()
    G.add_nodes_from(discords)
    G.add_edges_from(edges)
    
    plt.figure(figsize=(8, 6))
    pos = nx.spring_layout(G, seed=42)
    
    nx.draw_networkx_nodes(G, pos, node_color='lightblue', node_size=500)
    nx.draw_networkx_edges(G, pos, edge_color='gray', width=1.5)
    nx.draw_networkx_labels(G, pos, font_size=12, font_weight='bold')
    
    # Check connectivity
    n_vertices = len(discords)
    if n_vertices > 0:
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
        subtitle = "CONNECTED → ADJACENT" if connected else "DISCONNECTED → NONADJACENT"
    else:
        subtitle = "No discords"
    
    plt.title(f"{title}\n{subtitle}", fontsize=14)
    plt.axis('off')
    plt.tight_layout()
    plt.show()


def is_adjacent(P, Q, n, verbose=True):
    edges, discords = build_rigidity_graph(P, Q, n, verbose)
    
    if len(discords) <= 1:
        return True
    
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
    
    return all(visited)


# ============================================================================
# TEST EXAMPLES WITH GRAPH VISUALIZATION
# ============================================================================

def test_all_with_graphs():
    print("\n" + "=" * 70)
    print("PEDIGREE POLYTOPE ADJACENCY ALGORITHM")
    print("With NetworkX Graph Visualization")
    print("=" * 70)
    
    # Example 4.12 (adjacent)
    print("\n1. EXAMPLE 4.12 (adjacent)")
    P1 = [(1,2,3), (1,2,4), (2,3,5), (2,5,6)]
    Q1 = [(1,2,3), (1,2,4), (2,4,5), (2,3,6)]
    n = 6
    print(f"   Result: {'ADJACENT' if is_adjacent(P1, Q1, n, verbose=False) else 'NONADJACENT'}")
    draw_graph(P1, Q1, n, "Example 4.12: G_R")
    
    # Example 4.13 (nonadjacent)
    print("\n2. EXAMPLE 4.13 (nonadjacent)")
    P2 = [(1,2,3), (1,3,4), (2,3,5), (3,4,6)]
    Q2 = [(1,2,3), (1,2,4), (1,4,5), (1,3,6)]
    n = 6
    print(f"   Result: {'ADJACENT' if is_adjacent(P2, Q2, n, verbose=False) else 'NONADJACENT'}")
    draw_graph(P2, Q2, n, "Example 4.13: G_R")
    
    # Counterexample 4.8 (adjacent in pedigree)
    print("\n3. COUNTEREXAMPLE 4.8 (adjacent in pedigree)")
    P3 = [
        (1,2,3), (1,2,4), (1,3,5), (2,4,6), (2,6,7),
        (3,5,8), (1,4,9), (5,8,10)
    ]
    Q3 = [
        (1,2,3), (1,3,4), (2,3,5), (3,4,6), (4,6,7),
        (3,5,8), (1,4,9), (4,7,10)
    ]
    n = 10
    print(f"   Result: {'ADJACENT' if is_adjacent(P3, Q3, n, verbose=False) else 'NONADJACENT'}")
    draw_graph(P3, Q3, n, "Counterexample 4.8: G_R (Adjacent in Pedigree)")
    
    # Single discord
    print("\n4. SINGLE DISCORD (adjacent)")
    P4 = [(1,2,3), (1,2,4), (2,3,5), (2,5,6)]
    Q4 = [(1,2,3), (1,2,4), (2,3,5), (2,4,6)]
    n = 6
    print(f"   Result: {'ADJACENT' if is_adjacent(P4, Q4, n, verbose=False) else 'NONADJACENT'}")
    draw_graph(P4, Q4, n, "Single Discord: G_R")
    
    print("\n" + "=" * 70)
    print("All graphs displayed. Close each window to continue.")
    print("=" * 70)


if __name__ == "__main__":
    test_all_with_graphs()