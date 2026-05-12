#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Wrapper script for max-flow computation callable from Lean
Reads JSON input, computes max-flow, writes JSON output
"""

import json
import sys
from fractions import Fraction
from typing import List, Tuple, Dict, Any

# Import the max-flow implementation
from maxflowwithnodecaps import LayeredFlowNetwork, compute_max_flow


def parse_node_tuple(node_data: List[int]) -> Tuple[int, int, int]:
    """Parse node from JSON list to tuple"""
    if len(node_data) != 3:
        raise ValueError(f"Invalid node tuple: {node_data}")
    return (node_data[0], node_data[1], node_data[2])


def process_maxflow_request(input_data: Dict[str, Any]) -> Dict[str, Any]:
    """
    Process max-flow request from Lean
    
    Input format:
    {
        "nodes": [{"node": [i,j,k], "capacity": "num/den", "layer": l}, ...],
        "edges": [{"source": [i,j,k], "target": [i',j',k'], "capacity": "num/den"}, ...],
        "source": [i,j,k],
        "sink": [i',j',k']
    }
    
    Output format:
    {
        "maxFlow": "numerator/denominator",
        "success": true/false,
        "error": "error message" (optional)
    }
    """
    try:
        # Parse nodes
        nodes = []
        for node_data in input_data["nodes"]:
            node_triple = parse_node_tuple(node_data["node"])
            capacity_str = node_data["capacity"]
            layer = node_data["layer"]
            nodes.append((node_triple, capacity_str, layer))
        
        # Parse edges
        edges = []
        for edge_data in input_data["edges"]:
            source_triple = parse_node_tuple(edge_data["source"])
            target_triple = parse_node_tuple(edge_data["target"])
            capacity_str = edge_data["capacity"]
            edges.append((source_triple, target_triple, capacity_str))
        
        # Parse source and sink
        source = parse_node_tuple(input_data["source"])
        sink = parse_node_tuple(input_data["sink"])
        
        # Compute max-flow using existing function
        max_flow_str = compute_max_flow(nodes, edges, source, sink)
        
        return {
            "maxFlow": max_flow_str,
            "success": True,
            "error": None
        }
    
    except Exception as e:
        return {
            "maxFlow": "0/1",
            "success": False,
            "error": str(e)
        }


def main():
    """Main entry point for Lean integration"""
    if len(sys.argv) != 3:
        print("ERROR: Usage: maxflow_wrapper.py <input_json_file> <output_json_file>", 
              file=sys.stderr)
        sys.exit(1)
    
    input_file = sys.argv[1]
    output_file = sys.argv[2]
    
    try:
        # Read input JSON
        with open(input_file, 'r') as f:
            input_data = json.load(f)
        
        # Process request
        output_data = process_maxflow_request(input_data)
        
        # Write output JSON
        with open(output_file, 'w') as f:
            json.dump(output_data, f, indent=2)
        
        # Signal success to Lean
        print("SUCCESS")
        sys.exit(0)
    
    except FileNotFoundError as e:
        print(f"ERROR: File not found: {e}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"ERROR: Invalid JSON: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()