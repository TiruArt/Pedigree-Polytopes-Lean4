#!/usr/bin/env python3
import sys
print(f"Python executable: {sys.executable}")
print(f"Python version: {sys.version}")

try:
    import networkx as nx
    print(f"NetworkX version: {nx.__version__}")
    print("✓ NetworkX imported successfully!")
except ImportError as e:
    print(f"✗ Failed to import networkx: {e}")
    print("\nInstalled packages:")
    import subprocess
    subprocess.run([sys.executable, "-m", "pip", "list"])