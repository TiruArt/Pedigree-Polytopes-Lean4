#!/usr/bin/env python3
import sys, json
import networkx as nx
from networkx.algorithms.components import strongly_connected_components
from networkx.algorithms.bridges import bridges

input_data = sys.stdin.read()
residual_edges, num_vertices, original_edges, flow_edges = json.loads(input_data)

# Build residual graph
G = nx.DiGraph()
G.add_nodes_from(range(num_vertices))
for edge in residual_edges:
    G.add_edge(edge['from'], edge['to'])

# Find SCCs (Tarjan's algorithm)
sccs = list(strongly_connected_components(G))
vertex_to_scc = {}
for scc_id, scc in enumerate(sccs):
    for v in scc:
        vertex_to_scc[v] = scc_id

# Find interfaces (arcs between SCCs)
interfaces = []
for edge in original_edges:
    u, v = edge['from'], edge['to']
    if u in vertex_to_scc and v in vertex_to_scc:
        if vertex_to_scc[u] != vertex_to_scc[v]:
            interfaces.append([u, v])

# Find bridges within each SCC
bridges_list = []
for scc in sccs:
    if len(scc) <= 1:
        continue
    
    # Create undirected subgraph
    subgraph = nx.Graph()
    scc_nodes = set(scc)
    for edge in residual_edges:
        if edge['from'] in scc_nodes and edge['to'] in scc_nodes:
            subgraph.add_edge(edge['from'], edge['to'])
    
    # Find bridges
    if subgraph.number_of_edges() > 0:
        for u, v in bridges(subgraph):
            # Check if in original graph
            for edge in original_edges:
                if (edge['from'] == u and edge['to'] == v) or \
                   (edge['from'] == v and edge['to'] == u):
                    bridges_list.append([edge['from'], edge['to']])

# Combine and remove duplicates
frozen_arcs = list({tuple(a) for a in (interfaces + bridges_list)})
frozen_arcs = [list(a) for a in frozen_arcs]

result = {
    'frozenArcs': frozen_arcs,
    'interfaces': interfaces,
    'bridges': bridges_list,
    'sccs': [sorted(list(scc)) for scc in sccs]
}

print(json.dumps(result))