"""
m3p_runner.py  —  M3P Membership Checker
Generates input file for checking4membership and runs full M3P check.

Usage:
  python m3p_runner.py --n 5 --x 0.333 0.333 0.333 0.167 0.167 0.167 0.167 0.167 0.167
  python m3p_runner.py --file problem.txt

Results saved to: output\m3p_result_YYYYMMDD_HHMMSS.txt

Install package:
  pip install -i https://test.pypi.org/simple/ checking4membership

Reference:
  Arthanari, T.S. Pedigree Polytopes, Springer Nature 2023.
  GitHub: https://github.com/TiruArt/Pedigree-Polytopes-Lean4
"""

import os
import sys
import argparse
import subprocess
from datetime import datetime
from itertools import combinations

os.makedirs("output", exist_ok=True)

# ============================================================
# INPUT FILE FORMAT (sparse):
#
# Title line
# n
# i,j  i,j  ...   (edge for each non-zero entry)
# k    k    ...   (layer for each non-zero entry)
# x    x    ...   (value for each non-zero entry)
# True
# ============================================================

def build_input_file(n, x_values, title="M3P_Check"):
    """Convert dense X vector to sparse checking4membership input format."""
    lines = []
    lines.append(title)
    lines.append(str(n))

    # All triangles in order: layer 4,...,n
    all_tris = []
    for k in range(4, n+1):
        for i,j in combinations(range(1,k), 2):
            all_tris.append((i,j,k))

    # Filter non-zero entries
    nonzero = [(t, v) for t, v in zip(all_tris, x_values) if abs(v) > 1e-9]

    if not nonzero:
        # All zeros — write dummy
        nonzero = [(all_tris[0], 0.0)]

    edges  = "   ".join(f"{t[0]},{t[1]}" for t,_ in nonzero)
    layers = "   ".join(str(t[2]) for t,_ in nonzero)
    values = "   ".join(str(round(v,6)) for _,v in nonzero)

    lines.append(edges)
    lines.append(layers)
    lines.append(values)
    lines.append("True")

    return "\n".join(lines)

def run_checker(n, x_values, title="M3P_Check"):
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    infile  = f"output\\m3p_input_{ts}.txt"
    outdir  = f"output\\m3p_run_{ts}"
    os.makedirs(outdir, exist_ok=True)

    # Write input file
    content = build_input_file(n, x_values, title)
    with open(infile, "w", encoding="utf-8") as f:
        f.write(content)
    print(f"Input file: {infile}")
    print("Input:\n" + content)
    print("=" * 60)

    # Try to call checking4membership in headless mode
    try:
        import checking4membership
        print("Package: checking4membership loaded.")
        print("Running full M3P check...")
        print("=" * 60)

        # Call main() directly with input file and output dir
        import sys as _sys
        _old_argv = _sys.argv[:]
        _sys.argv = ["checking4membership", infile, outdir]
        try:
            from checking4membership.main import main as _main
            _main()
        except TypeError:
            # main() takes no args — pass via sys.argv
            from checking4membership import main as _main
            _main()
        finally:
            _sys.argv = _old_argv

        outfile = f"output\\m3p_result_{ts}.txt"
        # Collect output files from outdir
        out_files = os.listdir(outdir) if os.path.exists(outdir) else []
        with open(outfile, "w", encoding="utf-8") as f:
            f.write(f"Input file: {infile}\n")
            f.write(f"Output dir: {outdir}\n")
            f.write(f"Output files: {out_files}\n")
        print(f"Output files: {out_files}")
        print(f"Saved to: {outfile}")

    except ImportError:
        print("Note: checking4membership not installed.")
        print("Install: pip install -i https://test.pypi.org/simple/ checking4membership")
        print()
        print("Running P_MI(n) check only...")
        _pmi_check(n, x_values, ts)

def _pmi_check(n, x_values, ts):
    """Fallback: check X in P_MI(n) only."""
    passed = True
    lines = []
    neg = [v for v in x_values if v < -1e-9]
    if neg:
        lines.append(f"  FAIL: Non-negativity violated")
        passed = False
    else:
        lines.append("  OK:   Non-negativity satisfied")
    idx = 0
    for k in range(4, n+1):
        tris = list(combinations(range(1,k), 2))
        s = round(sum(x_values[idx:idx+len(tris)]), 3)
        if abs(s - 1.0) > 0.01:
            lines.append(f"  FAIL: Layer {k} sum = {s} != 1.0")
            passed = False
        else:
            lines.append(f"  OK:   Layer {k} sum = {s}")
        idx += len(tris)
    lines.append("")
    lines.append("  PASS: X in P_MI(n)" if passed else "  RESULT: X not in conv(P_n)")
    output = "\n".join(lines)
    print(output)
    outfile = f"output\\m3p_result_{ts}.txt"
    with open(outfile, "w", encoding="utf-8") as f:
        f.write(output)
    print(f"Saved to: {outfile}")

def main():
    parser = argparse.ArgumentParser(description="M3P Membership Checker")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--n", type=int, help="Number of cities")
    group.add_argument("--file", type=str, help="Existing problem.txt file")
    parser.add_argument("--x", type=float, nargs="+",
                        help="Dense input vector X (with --n)")
    parser.add_argument("--title", type=str, default="M3P_Check",
                        help="Problem title")
    args = parser.parse_args()

    if args.file:
        # Run directly on existing file
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        outdir = f"output\\m3p_run_{ts}"
        os.makedirs(outdir, exist_ok=True)
        import sys as _sys
        _old_argv = _sys.argv[:]
        _sys.argv = ["checking4membership", args.file, outdir]
        try:
            from checking4membership.main import main as _main
            _main()
        except Exception as e:
            print(f"Error: {e}")
        finally:
            _sys.argv = _old_argv
        out_files = os.listdir(outdir) if os.path.exists(outdir) else []
        print(f"Output files in {outdir}: {out_files}")
    else:
        if not args.x:
            print("Error: --x required with --n")
            sys.exit(1)
        run_checker(args.n, args.x, args.title)

if __name__ == "__main__":
    main()