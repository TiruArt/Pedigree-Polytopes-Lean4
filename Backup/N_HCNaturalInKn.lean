import Mathlib.Tactic

/-- Construct the sequence: [k, k+1, ..., n-1] ++ [0, 1, ..., k-1]. -/
def naturalSequence (n k : ℕ) (hk : k < n) : List (Fin n) :=
  List.pmap
    (fun i (hi : i < n) => (⟨i, hi⟩ : Fin n))
    ((List.range (n - k)).map (· + k) ++ List.range k)
    (by
      intro i hi
      simp [List.mem_append, List.mem_map, List.mem_range] at hi
      omega)

theorem naturalSequence_nodup {n : ℕ} (k : ℕ) (hk : k < n) :
  (naturalSequence n k hk).Nodup := by
  unfold naturalSequence
  apply List.Nodup.pmap
  · -- injectivity: Fin.mk is injective on val
    intro a ha b hb hab
    simp only [Fin.mk.injEq] at hab
    exact hab
  · -- underlying list is nodup
    apply List.Nodup.append
    · apply List.Nodup.map
      · intro a b hab; simp at hab; omega
      · exact List.nodup_range
    · exact List.nodup_range
    · intro x hx hy
      simp only [List.mem_map, List.mem_range] at hx hy
      obtain ⟨i, hi, rfl⟩ := hx
      omega
