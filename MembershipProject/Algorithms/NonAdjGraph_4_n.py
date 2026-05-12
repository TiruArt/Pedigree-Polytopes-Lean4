"""
Nonadjacency Graph for Pedigree Polytope
Corrected: Each Hamiltonian cycle counted once
"""

import itertools
import networkx as nx
import matplotlib.pyplot as plt
from collections import defaultdict
import time


# ============================================================================
# Helper functions
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


def is_valid_pedigree(triples, n):
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


def cycle_to_pedigree(cycle, n):
    """Convert a Hamiltonian cycle (list of vertices starting with 1) to pedigree"""
    current_cycle = list(cycle) + [cycle[0]]
    triples = []
    
    for k in range(n, 3, -1):
        idx = current_cycle.index(k)
        i = current_cycle[idx - 1]
        j = current_cycle[idx + 1]
        if i > j:
            i, j = j, i
        triples.append((i, j, k))
        current_cycle.pop(idx)
    
    triples.append((1, 2, 3))
    triples.reverse()
    return triples


def generate_all_pedigrees(n):
    """Generate all valid pedigrees for n (one per Hamiltonian cycle)"""
    vertices = list(range(2, n + 1))
    
    pedigrees = []
    seen_cycles = set()
    
    for perm in itertools.permutations(vertices):
        # Build cycle starting at 1
        cycle = [1] + list(perm)
        
        # Create canonical representation: cycle starting at 1, 
        # and ensure the second vertex < last vertex to avoid double-counting
        # (since cycle and its reverse are the same undirected cycle)
        second = cycle[1]
        last = cycle[-1]
        
        if second > last:
            # Reverse the order of vertices (excluding 1)
            rev_cycle = [1] + list(reversed(perm))
            canonical = tuple(rev_cycle)
        else:
            canonical = tuple(cycle)
        
        if canonical in seen_cycles:
            continue
        seen_cycles.add(canonical)
        
        # Convert to pedigree
        triples = cycle_to_pedigree(canonical, n)
        
        if is_valid_pedigree(triples, n):
            pedigrees.append(triples)
    
    return pedigrees


def build_rigidity_graph(P, Q, n):
    """Build G_R for two pedigrees"""
    discords = []
    for k in range(3, n + 1):
        idx = k - 3
        if P[idx] != Q[idx]:
            discords.append(k)
    
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
            
            # Condition 2
            for s in discords:
                if s >= q:
                    continue
                s_idx = s - 3
                if edge_of_triple(other[s_idx]) == (a, b):
                    edges.add((min(q, s), max(q, s)))
                    break
            
            # Condition 1
            if b <= 3:
                continue
            gen_layer = b
            if gen_layer not in discord_set:
                continue
            other_triple = other[gen_layer - 3]
            if other_triple not in generators(t):
                edges.add((min(q, gen_layer), max(q, gen_layer)))
    
    return edges, discords


def are_adjacent(P, Q, n):
    """Return True if adjacent (G_R connected)"""
    edges, discords = build_rigidity_graph(P, Q, n)
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
# Main computation
# ============================================================================

def compute_nonadjacency_graph(n):
    """Compute nonadjacency graph for pedigree polytope of size n"""
    print("=" * 70)
    print(f"NONADJACENCY GRAPH FOR PEDIGREE POLYTOPE n={n}")
    print("=" * 70)
    
    print("\nGenerating all valid pedigrees...")
    start_time = time.time()
    pedigrees = generate_all_pedigrees(n)
    m = len(pedigrees)
    elapsed = time.time() - start_time
    print(f"Found {m} valid pedigrees in {elapsed:.2f} seconds")
    
    expected = (n - 1) // 2  # Actually (n-1)!/2, but that's huge for n=6
    if n == 5:
        expected = 12
    elif n == 6:
        expected = 60
    print(f"Expected: {expected}")
    if m != expected:
        print(f"WARNING: Expected {expected}, got {m}")
    
    print(f"\nChecking {m * (m - 1) // 2} pairs...")
    start_time = time.time()
    
    nonadjacent_pairs = []
    
    for i in range(m):
        for j in range(i + 1, m):
            if not are_adjacent(pedigrees[i], pedigrees[j], n):
                nonadjacent_pairs.append((i + 1, j + 1))
    
    elapsed = time.time() - start_time
    print(f"Completed in {elapsed:.2f} seconds")
    
    print(f"\nTotal pairs: {m * (m - 1) // 2}")
    print(f"Adjacent pairs: {m * (m - 1) // 2 - len(nonadjacent_pairs)}")
    print(f"Nonadjacent pairs: {len(nonadjacent_pairs)}")
    
    # Draw nonadjacency graph if not too large
    if m <= 60:
        G = nx.Graph()
        G.add_nodes_from(range(1, m + 1))
        G.add_edges_from(nonadjacent_pairs)
        
        plt.figure(figsize=(14, 12))
        pos = nx.spring_layout(G, seed=42, k=1.5)
        nx.draw_networkx_nodes(G, pos, node_color='lightcoral', node_size=300)
        nx.draw_networkx_edges(G, pos, edge_color='gray', width=0.5)
        # nx.draw_networkx_labels(G, pos, font_size=6)
        plt.title(f"Nonadjacency Graph for Pedigree Polytope n={n}\n"
                  f"{m} vertices, {len(nonadjacent_pairs)} edges", fontsize=14)
        plt.axis('off')
        plt.tight_layout()
        plt.savefig(f"n{n}_nonadjacency_graph.png", dpi=150, bbox_inches='tight')
        print(f"\nGraph saved as n{n}_nonadjacency_graph.png")
    
    return pedigrees, nonadjacent_pairs


# ============================================================================
# Run for n=5 and n=6
# ============================================================================

if __name__ == "__main__":
    # n=5
    print("\n" + "=" * 70)
    print("RUNNING FOR n=5")
    print("=" * 70)
    p5, na5 = compute_nonadjacency_graph(5)
    print(f"\nNonadjacent pairs count: {len(na5)}")
    if len(na5) != 6:
        print(f"WARNING: Expected 6 nonadjacent pairs, got {len(na5)}")
    else:
        print("✓ Correct: 6 nonadjacent pairs found")
    
    # n=6
    print("\n" + "=" * 70)
    print("RUNNING FOR n=6")
    print("=" * 70)
    p6, na6 = compute_nonadjacency_graph(6)
    print(f"\nNonadjacent pairs count: {len(na6)}")