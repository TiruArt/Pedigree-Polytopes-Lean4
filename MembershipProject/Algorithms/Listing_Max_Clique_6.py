"""
List all Type A vertices (nonadjacency degree 10) with compact representations
for n=6
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
# Main: Find Type A vertices and list them
# ============================================================================

print("=" * 70)
print("LISTING ALL TYPE A VERTICES (nonadjacency degree 10) FOR n=6")
print("=" * 70)

print("\nGenerating all 60 pedigrees...")
start = time.time()
pedigrees = generate_all_pedigrees(6)
m = len(pedigrees)
print(f"  Generated {m} pedigrees in {time.time() - start:.2f}s")

print("\nComputing degrees...")
start = time.time()

degree = [0] * m

for i in range(m):
    for j in range(i + 1, m):
        if not are_adjacent(pedigrees[i], pedigrees[j], 6):
            degree[i] += 1
            degree[j] += 1

print(f"  Computation time: {time.time() - start:.2f}s")

# Find Type A vertices (degree 10)
type_a_indices = [i for i, d in enumerate(degree) if d == 10]
print(f"\nFound {len(type_a_indices)} Type A vertices (degree 10)")

if len(type_a_indices) == 0:
    print("No Type A vertices found!")
    print(f"Degree distribution: {sorted(set(degree))}")
    exit()

# Group Type A vertices by their pattern
print("\n" + "=" * 70)
print("TYPE A VERTICES (Clique members)")
print("=" * 70)

# Group by k=4 edge
by_k4 = defaultdict(list)
by_pattern = defaultdict(list)

for idx in type_a_indices:
    p = pedigrees[idx]
    e4 = p[1][:2]
    e5 = p[2][:2]
    e6 = p[3][:2]
    compact_str = compact(p)
    by_k4[e4].append(compact_str)
    by_pattern[(e4, e5, e6)].append(idx)

print(f"\nTotal: {len(type_a_indices)} vertices\n")

# Sort by k=4 edge
for e4 in sorted(by_k4.keys()):
    compacts = sorted(by_k4[e4])
    print(f"k4 = {e4}: {len(compacts)} vertices")
    for comp in compacts:
        print(f"    {comp}")
    print()

# Also show the full triples for the first few
print("\n" + "=" * 70)
print("FULL TRIPLES FOR FIRST 5 TYPE A VERTICES")
print("=" * 70)
for idx in type_a_indices[:5]:
    p = pedigrees[idx]
    print(f"\nP{idx+1}: {compact(p)}")
    print(f"  k=3: {p[0]}")
    print(f"  k=4: {p[1]}")
    print(f"  k=5: {p[2]}")
    print(f"  k=6: {p[3]}")

# Analyze the pattern
print("\n" + "=" * 70)
print("PATTERN ANALYSIS")
print("=" * 70)

# Count by k=4 edge
print("\nDistribution by k=4 edge:")
for e4, compacts in sorted(by_k4.items()):
    print(f"  {e4}: {len(compacts)} vertices")

# Check if all Type A have the same k=4 edge
if len(by_k4) == 1:
    print("\n✓ All Type A vertices share the same k=4 edge!")
    common_e4 = list(by_k4.keys())[0]
    print(f"  Common k4 = {common_e4}")
else:
    print(f"\nType A vertices have {len(by_k4)} different k=4 edges")

# Show the pattern for the most common k4
most_common_k4 = max(by_k4.items(), key=lambda x: len(x[1]))
print(f"\nMost common k4: {most_common_k4[0]} with {len(most_common_k4[1])} vertices")

print("\n" + "=" * 70)