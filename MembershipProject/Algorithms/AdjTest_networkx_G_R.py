"""
Pedigree Polytope Adjacency Algorithm with NetworkX
Saves all graphs as PNG files in 'graphs/' directory
"""

import networkx as nx
import matplotlib.pyplot as plt
import os
from collections import deque


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

def build_rigidity_graph(P, Q, n, verbose=False):
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


def is_adjacent(P, Q, n, verbose=False):
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
# GRAPH VISUALIZATION - SAVE TO FILE
# ============================================================================

def save_graph(P, Q, n, title, filename):
    """Draw G_R and save to file"""
    edges, discords = build_rigidity_graph(P, Q, n, verbose=False)
    
    if len(discords) == 0:
        print(f"  {title}: No discords → P = Q")
        return False
    
    G = nx.Graph()
    G.add_nodes_from(discords)
    G.add_edges_from(edges)
    
    # Check connectivity
    connected = is_adjacent(P, Q, n, verbose=False)
    
    # Create figure
    plt.figure(figsize=(10, 8))
    pos = nx.spring_layout(G, seed=42)
    
    # Draw nodes
    nx.draw_networkx_nodes(G, pos, node_color='lightblue', node_size=600)
    nx.draw_networkx_edges(G, pos, edge_color='gray', width=2)
    nx.draw_networkx_labels(G, pos, font_size=14, font_weight='bold')
    
    # Add title with result
    result = "ADJACENT" if connected else "NONADJACENT"
    status = "CONNECTED → " + result if connected else "DISCONNECTED → " + result
    plt.title(f"{title}\n\nG_R: {status}", fontsize=14, pad=20)
    plt.axis('off')
    plt.tight_layout()
    
    # Save to file
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"  ✓ {title}: {result} → saved to {filename}")
    return True


# ============================================================================
# TEST EXAMPLES
# ============================================================================

def run_all_examples():
    """Run all examples and save graphs as PNG files"""
    
    # Create output directory
    os.makedirs("graphs", exist_ok=True)
    
    examples = []
    
    # Example 4.12 (adjacent)
    examples.append({
        'name': "Example 4.12",
        'desc': "Adjacent (G_R connected)",
        'filename': "graphs/example_412.png",
        'P': [(1,2,3), (1,2,4), (2,3,5), (2,5,6)],
        'Q': [(1,2,3), (1,2,4), (2,4,5), (2,3,6)],
        'n': 6
    })
    
    # Example 4.13 (nonadjacent)
    examples.append({
        'name': "Example 4.13",
        'desc': "Nonadjacent (G_R disconnected)",
        'filename': "graphs/example_413.png",
        'P': [(1,2,3), (1,3,4), (2,3,5), (3,4,6)],
        'Q': [(1,2,3), (1,2,4), (1,4,5), (1,3,6)],
        'n': 6
    })
    
    # Single discord (adjacent)
    examples.append({
        'name': "Single Discord",
        'desc': "Adjacent (|D|=1)",
        'filename': "graphs/single_discord.png",
        'P': [(1,2,3), (1,2,4), (2,3,5), (2,5,6)],
        'Q': [(1,2,3), (1,2,4), (2,3,5), (2,4,6)],
        'n': 6
    })
    
    # Counterexample 4.8 (adjacent in pedigree)
    examples.append({
        'name': "Counterexample 4.8",
        'desc': "Adjacent in pedigree (nonadjacent in STSP)",
        'filename': "graphs/counterexample_48.png",
        'P': [
            (1,2,3), (1,2,4), (1,3,5), (2,4,6), (2,6,7),
            (3,5,8), (1,4,9), (5,8,10)
        ],
        'Q': [
            (1,2,3), (1,3,4), (2,3,5), (3,4,6), (4,6,7),
            (3,5,8), (1,4,9), (4,7,10)
        ],
        'n': 10
    })
    
    # Example 4.15 (nonadjacent, disconnected)
    examples.append({
        'name': "Example 4.15",
        'desc': "Nonadjacent (G_R disconnected)",
        'filename': "graphs/example_415.png",
        'P': [(1,2,3), (1,3,4), (2,3,5), (3,4,6)],
        'Q': [(1,2,3), (1,2,4), (1,4,5), (1,3,6)],
        'n': 6
    })
    
    # Example 4.16 (adjacent, n=7)
    examples.append({
        'name': "Example 4.16",
        'desc': "Adjacent (n=7)",
        'filename': "graphs/example_416.png",
        'P': [(1,2,3), (2,3,4), (2,4,5), (2,5,6), (2,6,7)],
        'Q': [(1,2,3), (1,3,4), (1,4,5), (1,5,6), (1,6,7)],
        'n': 7
    })
    
    # Example 4.17 (adjacent from the text)
    examples.append({
        'name': "Example 4.17",
        'desc': "Adjacent (connected G_R)",
        'filename': "graphs/example_417.png",
        'P': [(1,2,3), (1,2,4), (2,3,5), (2,4,6), (2,5,7)],
        'Q': [(1,2,3), (1,2,4), (2,3,5), (2,4,6), (2,6,7)],
        'n': 7
    })
    
    print("\n" + "=" * 70)
    print("PEDIGREE POLYTOPE ADJACENCY ALGORITHM")
    print(f"Saving graphs to 'graphs/' directory...")
    print("=" * 70)
    print()
    
    results = {}
    for ex in examples:
        title = f"{ex['name']}: {ex['desc']}"
        success = save_graph(ex['P'], ex['Q'], ex['n'], title, ex['filename'])
        results[ex['name']] = success
    
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    for name, result in results.items():
        status = "✓ Saved" if result else "✗ No discords"
        print(f"{name:25} → {status}")
    
    print("\n" + "=" * 70)
    print(f"All graphs saved to: {os.path.abspath('graphs')}")
    print("=" * 70)


if __name__ == "__main__":
    run_all_examples()