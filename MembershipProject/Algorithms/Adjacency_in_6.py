"""
Compute full degree distribution for n=6
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
# Main computation for n=6
# ============================================================================

print("=" * 70)
print("COMPUTING DEGREE DISTRIBUTION FOR n=6")
print("=" * 70)

print("\nStep 1: Generating all 60 pedigrees...")
start = time.time()
pedigrees = generate_all_pedigrees(6)
m = len(pedigrees)
print(f"  Generated {m} pedigrees in {time.time() - start:.2f}s")

if m != 60:
    print(f"  ERROR: Expected 60, got {m}")
    exit()

print("\nStep 2: Computing nonadjacent degrees...")
start = time.time()

degree = [0] * m

total_pairs = m * (m - 1) // 2
pairs_checked = 0

for i in range(m):
    for j in range(i + 1, m):
        if not are_adjacent(pedigrees[i], pedigrees[j], 6):
            degree[i] += 1
            degree[j] += 1
        pairs_checked += 1
        if pairs_checked % 500 == 0:
            print(f"  Processed {pairs_checked}/{total_pairs} pairs...")

print(f"  Computation time: {time.time() - start:.2f}s")

# ============================================================================
# Analyze results
# ============================================================================

print("\n" + "=" * 70)
print("RESULTS")
print("=" * 70)

# Degree distribution
degree_counts = defaultdict(int)
for d in degree:
    degree_counts[d] += 1

print("\nDegree Distribution in Nonadjacency Graph:")
print("  Degree : Count")
for d in sorted(degree_counts.keys()):
    print(f"    {d:2}    : {degree_counts[d]:2}")

# Find the two types mentioned
print("\n" + "=" * 70)
print("ANALYSIS")
print("=" * 70)

# Look for degrees 10 and 11
count_10 = degree_counts.get(10, 0)
count_11 = degree_counts.get(11, 0)

print(f"\nType A (degree 10): {count_10} vertices")
print(f"Type B (degree 11): {count_11} vertices")
print(f"Other degrees: {[d for d in degree_counts.keys() if d not in [10, 11]]}")

# Verify total
if count_10 + count_11 == m:
    print(f"\n✓ All vertices have degree 10 or 11")
else:
    print(f"\n✗ Not all vertices have degree 10 or 11 (found {count_10 + count_11} out of {m})")

# Find examples
print("\n" + "=" * 70)
print("EXAMPLES")
print("=" * 70)

# Find a degree 10 vertex
deg_10_indices = [i for i, d in enumerate(degree) if d == 10]
if deg_10_indices:
    idx10 = deg_10_indices[0]
    print(f"\nDegree 10 example (P{idx10+1}):")
    print(f"  Compact: {compact(pedigrees[idx10])}")
    print(f"  Full: {pedigrees[idx10]}")

# Find a degree 11 vertex
deg_11_indices = [i for i, d in enumerate(degree) if d == 11]
if deg_11_indices:
    idx11 = deg_11_indices[0]
    print(f"\nDegree 11 example (P{idx11+1}):")
    print(f"  Compact: {compact(pedigrees[idx11])}")
    print(f"  Full: {pedigrees[idx11]}")

# Compute maximum clique size
# Maximum clique in adjacency graph = size of largest set with no nonadjacent edges
# = size of largest independent set in nonadjacency graph
# Since nonadjacency graph likely has vertices of degree 10 and 11,
# and vertices of same degree might be adjacent to each other? Need to check.

print("\n" + "=" * 70)
print("MAXIMUM CLIQUE SIZE")
print("=" * 70)

# If vertices of same degree are all mutually adjacent, then the larger type gives a clique
if count_10 >= count_11:
    max_clique = count_10
    print(f"\nAssuming Type A (deg 10) are mutually adjacent, max clique = {count_10}")
else:
    max_clique = count_11
    print(f"\nAssuming Type B (deg 11) are mutually adjacent, max clique = {count_11}")

print(f"\nBased on the degree distribution, the maximum clique size is at least {max_clique}")
print("To confirm, we would need to check whether vertices within each type are all mutually adjacent.")

print("\n" + "=" * 70)