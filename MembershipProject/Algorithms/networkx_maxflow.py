#!/usr/bin/env python3
import sys, json
import networkx as nx

input_data = sys.stdin.read()
data = json.loads(input_data)

G = nx.DiGraph()
for i in range(data['numVertices']):
    G.add_node(i)

for edge in data['edges']:
    G.add_edge(edge['from'], edge['to'], capacity=edge['capacity'])

flow_value, flow_dict = nx.maximum_flow(G, data['source'], data['sink'])

flow_edges = []
for u in flow_dict:
    for v in flow_dict[u]:
        if flow_dict[u][v] > 0:
            flow_edges.append([u, v, int(flow_dict[u][v])])

result = {
    'maxFlowValue': int(flow_value),
    'flowEdges': flow_edges
}

print(json.dumps(result))