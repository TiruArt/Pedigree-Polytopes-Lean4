def build_rigidity_graph(P, Q):
    """
    P, Q: lists of triples (i, j, k) for k = 3..n, with P[0] = (1,2,3)
    Returns: adjacency list of G_R on discords
    """
    n = len(P)  # n = number of vertices (since layers 3..n)
    
    # Step 1: Find discords
    discords = []
    for k in range(3, n+1):
        idx = k - 3  # index in list
        if P[idx] != Q[idx]:
            discords.append(k)
    
    # Map discord to index for graph building
    discord_set = set(discords)
    discord_index = {k: i for i, k in enumerate(discords)}
    
    # Step 2: Build edges
    edges = set()
    
    # Process discords from largest to smallest
    for q in sorted(discords, reverse=True):
        q_idx = q - 3
        
        # For each pedigree i = 0,1 (P and Q)
        for i in [0, 1]:
            e = (P[q_idx] if i == 0 else Q[q_idx])
            a, b, _ = e
            other = Q if i == 0 else P
            
            # Condition 2: edge already appears in other pedigree at earlier discord
            for s in discords:
                if s >= q:
                    continue
                s_idx = s - 3
                if edge_of_triple(other[s_idx]) == (a, b):
                    edges.add((min(q, s), max(q, s)))
                    break  # once welded, no need to check further for this i
            
            # Condition 1: generator missing
            if b <= 3:
                continue  # generator is (1,2,3), always available
            gen_layer = b
            if gen_layer not in discord_set:
                continue  # generator at non-discord, always available in other
            # Check if generator is available in other
            gen_triple = (a, b, b) if b > 3 else (1,2,3)  # but for b>3, generator is (a,b,b)
            # Actually, generator must be of form (r,a,b) or (a,s,b)
            # In a valid pedigree, other[gen_layer-3] is a generator of e
            other_triple = other[gen_layer - 3]
            if other_triple not in generators(e):
                # generator missing → weld
                edges.add((min(q, gen_layer), max(q, gen_layer)))
    
    return edges, discords


def edge_of_triple(t):
    return (t[0], t[1])


def generators(t):
    """Return set of generator triples for t = (a,b,k)"""
    a, b, k = t
    if a == 1 and b == 2:
        return set()
    if b > 3:
        gen = set()
        for r in range(1, a):
            gen.add((r, a, b))
        for s in range(a+1, b):
            gen.add((a, s, b))
        return gen
    else:
        return {(1, 2, 3)}


def is_adjacent(P, Q):
    """Return True if P and Q are adjacent in the pedigree polytope"""
    edges, discords = build_rigidity_graph(P, Q)
    
    # If no discords, P == Q? Actually they must be distinct? Adjacent requires distinct? Let's handle:
    if len(discords) <= 1:
        return True  # |D| = 0 or 1 → adjacent (|D|=0 means P=Q, trivially adjacent)
    
    # Build adjacency list for BFS
    n_vertices = len(discords)
    adj = {i: [] for i in range(n_vertices)}
    discord_index = {k: i for i, k in enumerate(discords)}
    for s, t in edges:
        adj[discord_index[s]].append(discord_index[t])
        adj[discord_index[t]].append(discord_index[s])
    
    # Check connectivity
    visited = [False] * n_vertices
    stack = [0]
    visited[0] = True
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if not visited[v]:
                visited[v] = True
                stack.append(v)
    
    return all(visited)  # connected if all visited


# Example from Chapter 4 (Example 4.12)
P = [(1,2,3), (1,2,4), (2,3,5), (2,5,6)]
Q = [(1,2,3), (1,2,4), (2,4,5), (2,3,6)]

print("Adjacent?", is_adjacent(P, Q))  # Should return True (adjacent)