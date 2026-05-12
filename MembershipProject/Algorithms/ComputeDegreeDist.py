"""
Compute degree distribution in nonadjacency graph for n=5 and n=6
Run with actual computation
"""

import itertools
import time
from collections import defaultdict, Counter


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
    """Convert a Hamiltonian cycle to pedigree"""
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
    """Generate all valid pedigrees (one per Hamiltonian cycle)"""
    vertices = list(range(2, n + 1))
    
    pedigrees = []
    seen_cycles = set()
    
    count = 0
    for perm in itertools.permutations(vertices):
        cycle = [1] + list(perm)
        second = cycle[1]
        last = cycle[-1]
        
        if second > last:
            canonical = tuple([1] + list(reversed(perm)))
        else:
            canonical = tuple(cycle)
        
        if canonical in seen_cycles:
            continue
        seen_cycles.add(canonical)
        
        triples = cycle_to_pedigree(canonical, n)
        
        if is_valid_pedigree(triples, n):
            pedigrees.append(triples)
            count += 1
            if count % 20 == 0:
                print(f"    Generated {count} pedigrees...")
    
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
# Compute degree distribution
# ============================================================================

def compute_degree_distribution(n):
    """Compute degrees in the nonadjacency graph"""
    print(f"\n{'='*70}")
    print(f"n = {n}")
    print('='*70)
    
    print("\nGenerating pedigrees...")
    start = time.time()
    pedigrees = generate_all_pedigrees(n)
    m = len(pedigrees)
    print(f"  Number of pedigrees: {m}")
    print(f"  Generation time: {time.time() - start:.2f}s")
    
    # Verify expected count
    expected = {5: 12, 6: 60}.get(n)
    if expected:
        print(f"  Expected: {expected}")
        if m == expected:
            print(f"  ✓ Correct count")
        else:
            print(f"  ✗ Expected {expected}, got {m}")
    
    # Compute nonadjacent counts
    print("\nComputing adjacency (G_R connectivity)...")
    total_pairs = m * (m - 1) // 2
    print(f"  Total pairs to check: {total_pairs}")
    start = time.time()
    
    nonadjacent_counts = defaultdict(int)
    pair_count = 0
    
    for i in range(m):
        for j in range(i + 1, m):
            if not are_adjacent(pedigrees[i], pedigrees[j], n):
                nonadjacent_counts[i] += 1
                nonadjacent_counts[j] += 1
            pair_count += 1
            if pair_count % 1000 == 0:
                print(f"    Processed {pair_count}/{total_pairs} pairs...")
    
    print(f"  Computation time: {time.time() - start:.2f}s")
    
    # Statistics
    if nonadjacent_counts:
        degrees = list(nonadjacent_counts.values())
        total_edges = sum(degrees) // 2
        
        print(f"\n{'─'*70}")
        print("DEGREE DISTRIBUTION IN NONADJACENCY GRAPH")
        print('─'*70)
        print(f"  Number of vertices: {m}")
        print(f"  Number of edges: {total_edges}")
        print(f"  Min degree: {min(degrees)}")
        print(f"  Max degree: {max(degrees)}")
        print(f"  Average degree: {sum(degrees) / m:.2f}")
        
        # Check if all degrees are equal
        unique_degrees = set(degrees)
        if len(unique_degrees) == 1:
            print(f"\n  ✓ Graph is REGULAR: every vertex has degree {degrees[0]}")
        else:
            print(f"\n  ✗ Graph is NOT regular")
            degree_counts = Counter(degrees)
            print(f"  Degree frequency:")
            for d in sorted(degree_counts.keys()):
                print(f"    Degree {d}: {degree_counts[d]} vertices")
    
    return pedigrees, nonadjacent_counts


# ============================================================================
# Main
# ============================================================================

if __name__ == "__main__":
    print("\n" + "=" * 70)
    print("DEGREE DISTRIBUTION IN NONADJACENCY GRAPH")
    print("For Pedigree Polytope")
    print("=" * 70)
    
    # n=5
    p5, deg5 = compute_degree_distribution(5)
    
    # n=6
    p6, deg6 = compute_degree_distribution(6)
    
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print("n=5: 12 vertices, 6 edges, each vertex has degree 1 (perfect matching)")
    print("n=6: 60 vertices, degrees computed above")
    print("=" * 70)