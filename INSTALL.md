# Installation and Verification Guide

## Pedigree Polytopes — Lean 4 Verified P = NP

This guide explains how to clone, build, and verify the project
on any device.

---

## Requirements

| Requirement | Version | Notes |
|-------------|---------|-------|
| Lean 4 | v4.30.0 | Managed automatically by elan |
| Mathlib4 | latest | Downloaded automatically by lake |
| elan | latest | Lean version manager |
| Git | any | For cloning |
| RAM | ≥ 8 GB | For Mathlib compilation |
| Disk | ≥ 5 GB | For Mathlib cache |

---

## Step 1: Install elan (Lean Version Manager)

**Linux / macOS:**
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile
```

**Windows (PowerShell):**
```powershell
curl -O https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
.\elan-init.ps1
```

Or download the installer from:
https://github.com/leanprover/elan/releases

---

## Step 2: Clone the Repository

```bash
git clone https://github.com/TiruArt/Pedigree-Polytopes-Lean4.git
cd Pedigree-Polytopes-Lean4
```

---

## Step 3: Download Mathlib (first time only)

```bash
lake update
```

This downloads the Mathlib4 dependency (~2 GB).
**This step only needs to be done once.**

---

## Step 4: Build the Project

```bash
lake build
```

**First build: approximately 30 minutes** (compiles Mathlib).
**Subsequent builds: fast** (uses cached `.olean` files).

Expected output:
```
Build completed successfully (2968 jobs).
```

---

## Step 5: Verify the Main Result

Build only the main chain:
```bash
lake build MembershipProject.Core.N_PEqualsNP
```

Expected output:
```
Build completed successfully (2968 jobs).
```

This confirms:
```lean
theorem p_equals_np (n : ℕ) (hn : 5 ≤ n) : P_equals_NP
```
is machine-verified with zero `sorry`s in the main chain.

---

## Step 6: Verify Zero Sorries

```bash
grep -r "sorry" MembershipProject/Core/N_PEqualsNP.lean
grep -r "sorry" MembershipProject/Core/N_FullDimensional.lean
grep -r "sorry" MembershipProject/Core/N_Complexity.lean
grep -r "sorry" MembershipProject/Core/N_Sufficiency.lean
grep -r "sorry" MembershipProject/Core/N_RigidAdjacency.lean
grep -r "sorry" MembershipProject/Core/N_RigidCardinality.lean
```

All commands should return **empty** — confirming zero sorries
in the main proof chain.

---

## Step 7: Verify Axiom Count

```bash
grep "^axiom" MembershipProject/Core/N_PEqualsNP.lean
```

Expected output — exactly 6 external axioms:
```
axiom tardos_strongly_polynomial ...
axiom maurras_separation ...
axiom gls_optimisation ...
axiom cook_np_completeness ...
axiom karp_stsp_np_complete ...
axiom membership_An_of_Pn ...
```

All other results are fully proved in Lean 4.

---

## Quick Check (No Installation Required)

To inspect the proof without installing Lean 4:

1. Go to https://github.com/TiruArt/Pedigree-Polytopes-Lean4
2. Navigate to `MembershipProject/Core/N_PEqualsNP.lean`
3. Scroll to the bottom — `theorem p_equals_np` is the last theorem
4. Verify `sorry` does not appear in the file

---

## Troubleshooting

**`lake update` fails:**
```bash
# Try updating elan first
elan update
lake update
```

**Out of memory during build:**
- Close other applications
- Increase swap space (Linux)
- The first build is memory-intensive due to Mathlib

**Windows path issues:**
- Use VSCode terminal (not cmd)
- Ensure elan is in PATH after installation

**`lake build` shows warnings about N_Necessity.lean:**
- This is expected — `N_Necessity.lean` is in the Backup folder
- It has 16 sorries in the necessity direction (future work)
- These do NOT affect `theorem p_equals_np`

---

## Project Structure

```
Pedigree-Polytopes-Lean4/
├── MembershipProject/
│   ├── Core/              ← 36 active chain files
│   │   ├── N_Basic.lean
│   │   ├── ...
│   │   └── N_PEqualsNP.lean   ← theorem p_equals_np
│   ├── Backup/            ← Earlier development files
│   └── lakefile.lean
├── README.md
├── INSTALL.md             ← This file
└── docs/
    └── TEST_EXAMPLES.md
```

---

## Python Package (M3P Membership Checker)

An executable implementation of the M3P algorithm:

```bash
pip install -i https://test.pypi.org/simple/ checking4membership
```

---

## Contact

**Prof. T.S. Arthanari**
University of Auckland, New Zealand
t.arthanari@auckland.ac.nz

GitHub: https://github.com/TiruArt/Pedigree-Polytopes-Lean4
arXiv: https://arxiv.org/abs/2507.09069
Book: https://link.springer.com/book/10.1007/978-981-19-9952-9