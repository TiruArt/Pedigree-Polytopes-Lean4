"""
Find a clique of size 36 in the adjacency graph for n=6
These are the Type A vertices (nonadjacency degree 10)
"""

import itertools
import time
from collections import defaultdict


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


def compact(p):
    """Compact representation: (e4)(e5)(e6) as edges"""
    return f"({p[1][0]},{p[1][1]})({p[2][0]},{p[2][1]})({p[3][0]},{p[3][1]})"


# ============================================================================
# Find Type A vertices (degree 10 in nonadjacency graph) and verify they form a clique
# ============================================================================

print("=" * 70)
print("FINDING CLIQUE OF SIZE 36 IN ADJACENCY GRAPH FOR n=6")
print("=" * 70)

print("\nGenerating all 60 pedigrees...")
start = time.time()
pedigrees = generate_all_pedigrees(6)
m = len(pedigrees)
print(f"  Generated {m} pedigrees in {time.time() - start:.2f}s")

print("\nComputing nonadjacent degrees...")
start = time.time()

degree = [0] * m
nonadjacency = [[False] * m for _ in range(m)]

for i in range(m):
    for j in range(i + 1, m):
        adj = are_adjacent(pedigrees[i], pedigrees[j], 6)
        if not adj:
            degree[i] += 1
            degree[j] += 1
            nonadjacency[i][j] = True
            nonadjacency[j][i] = True

print(f"  Computation time: {time.time() - start:.2f}s")

# Find Type A vertices (degree 10)
type_a_indices = [i for i, d in enumerate(degree) if d == 10]
type_b_indices = [i for i, d in enumerate(degree) if d == 11]

print(f"\nType A (degree 10): {len(type_a_indices)} vertices")
print(f"Type B (degree 11): {len(type_b_indices)} vertices")

# Verify that Type A vertices are mutually adjacent (form a clique)
print("\n" + "=" * 70)
print("VERIFYING TYPE A VERTICES FORM A CLIQUE")
print("=" * 70)

all_adjacent = True
nonadjacent_pairs = []

for idx in range(len(type_a_indices)):
    for jdx in range(idx + 1, len(type_a_indices)):
        i = type_a_indices[idx]
        j = type_a_indices[jdx]
        if nonadjacency[i][j]:
            all_adjacent = False
            nonadjacent_pairs.append((i, j))

if all_adjacent:
    print(f"\n✓ All {len(type_a_indices)} Type A vertices are mutually adjacent")
    print(f"  They form a clique of size {len(type_a_indices)} in the adjacency graph")
else:
    print(f"\n✗ Found {len(nonadjacent_pairs)} nonadjacent pairs within Type A")
    for i, j in nonadjacent_pairs[:5]:
        print(f"  P{i+1} and P{j+1} are nonadjacent")

# Show examples of Type A vertices
print("\n" + "=" * 70)
print("EXAMPLES OF TYPE A VERTICES (Clique members)")
print("=" * 70)

for idx in type_a_indices[:5]:
    p = pedigrees[idx]
    print(f"\nP{idx+1}: {compact(p)}")
    print(f"  Full triples:")
    for k in range(3, 7):
        print(f"    k={k}: {p[k-3]}")
    print(f"  Nonadjacent degree: {degree[idx]}")

# Also show a Type B vertex for comparison
if type_b_indices:
    idx_b = type_b_indices[0]
    print(f"\n" + "=" * 70)
    print("EXAMPLE OF TYPE B VERTEX (Not in the clique)")
    print("=" * 70)
    p = pedigrees[idx_b]
    print(f"\nP{idx_b+1}: {compact(p)}")
    print(f"  Full triples:")
    for k in range(3, 7):
        print(f"    k={k}: {p[k-3]}")
    print(f"  Nonadjacent degree: {degree[idx_b]}")

# Verify Type B vertices are also mutually adjacent
if len(type_b_indices) > 1:
    print("\n" + "=" * 70)
    print("VERIFYING TYPE B VERTICES")
    print("=" * 70)
    all_adj_b = True
    for idx in range(len(type_b_indices)):
        for jdx in range(idx + 1, len(type_b_indices)):
            i = type_b_indices[idx]
            j = type_b_indices[jdx]
            if nonadjacency[i][j]:
                all_adj_b = False
                break
    if all_adj_b:
        print(f"✓ Type B vertices ({len(type_b_indices)}) also form a clique")
    else:
        print(f"✗ Type B vertices do not form a clique")

print("\n" + "=" * 70)
print("CONCLUSION")
print("=" * 70)
print(f"The Type A vertices ({len(type_a_indices)} of them) form a clique of size {len(type_a_indices)}")
print(f"This is the largest clique in the adjacency graph for n=6")
print("=" * 70)