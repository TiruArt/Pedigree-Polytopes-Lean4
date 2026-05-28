# Pedigree Polytope Lean 4 Formalization — Persistent Rules

## CRITICAL: h_distinct applies only for k ≥ 4

`h_distinct` in `Pedigree n` is stated as:
```lean
h_distinct : ∀ i j,
  ∀ hi : i < triangles.length,
  ∀ hj : j < triangles.length,
  i > 0 → j > 0 → i ≠ j →   -- BOTH positions must be > 0
  (triangles.get ⟨i, hi⟩).i ≠ (triangles.get ⟨j, hj⟩).i ∨
  (triangles.get ⟨i, hi⟩).j ≠ (triangles.get ⟨j, hj⟩).j
```

**The base triangle `(1,2,3)` at position 0 (layer 3) is EXCLUDED from h_distinct.**

`h_distinct` applies only to triangles at layers ≥ 4 (positions > 0).

### Consequence for `hne` in `Pedigree.extend`
To prove `hne` (new pair differs from all existing pairs), do NOT use `h_distinct`.
Instead use `h_in_delta` + `h_layers`:
- Every triangle at position i has `.j < .k = i + 3 ≤ n - 1 < n`
- New triangle has `.j = n` (from `Delta (n+1)`)
- So new `.j = n > n-1 ≥` every existing `.j`
- This works for ALL positions including position 0

```lean
lemma pedigree_hne (P : Pedigree n) (a b : ℕ) (hab : a < b) (hbn : b = n) :
    ∀ i, ∀ hi : i < P.triangles.length,
      (P.triangles.get ⟨i, hi⟩).i ≠ a ∨
      (P.triangles.get ⟨i, hi⟩).j ≠ b := by
  intro i hi
  right  -- prove .j ≠ b
  -- .j < .k ≤ n - 1 < n = b
  have hlayer := P.h_layers i hi
  have hlen   := P.h_length
  have hn     := P.h_n
  have hjk    := mem_Delta_jl (P.h_in_delta i hi)
  simp only [Triple.k] at hjk hlayer
  omega
```

## Other Key Rules

### Triple structure
`Triple = ℕ × ℕ × ℕ` with `.i = .1`, `.j = .2.1`, `.k = .2.2`

### Pedigree(n) structure
- `n-2` triangles at layers 3, 4, ..., n
- First triangle always `(1,2,3)` at layer 3 (position 0)
- `h_distinct`: distinct pairs for layers ≥ 4 ONLY

### partialPedigree k i j : Pedigree (k-1)
- Gives a `(k-1)`-pedigree (layers 3..k-1) with `(i,j)` in last `(k-1)`-tour
- To get a k-tour containing `(i,j)`: use `partialPedigree (k+1) i j : Pedigree k`

### Selection Lemma indexing (Chapter 7)
- `partialPedigree (k+1) i j : Pedigree k` = k-tour with `(i,j)` as generator
- Extend by `(i,j,k+1)` → `Pedigree (k+1)`, `x_{k+1}(i,j) = 1`
- Extend by `(i,k+1,k+2)` → `Pedigree (k+2)`, `x_{k+2}(i,k+1) = 1`
- Default chain to `Pedigree n`

### Induction direction for coeff_zero
- Upward from k=4 to n
- IH: `C(a,b,m) = 0` for all non-default `(a,b,m)` with `m ≤ k`
- Three pedigrees P1,P2,P3 from Chapter 7 prove `C(i,j,k+1) = 0`

### hpair (distinct insertion pairs)
- `{i,j}` is never an insertion pair in `partialPedigree`
- Proved by Cases [a] and [b] (Tiru) + Python verification k=4..12
- Cases [a] (i∈{1,2,3}): pairs are `{q1,q2},{q2,4},...,{i,q1},{q1,j},...` — never `{i,j}`
- Cases [b] (i≥4): pairs are `{l-2,l-1}` for 4≤l≤j-1, then `{i-2,i}`, then `{i-2,j}`,... — never `{i,j}`