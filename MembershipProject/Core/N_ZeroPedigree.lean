import MembershipProject.Core.N_HypSum
import Mathlib.Tactic

namespace MembershipProject.Core

def zeroTriangle (i : ℕ) : Triple := (i+1, i+2, i+3)
def zeroTriangles (n : ℕ) : List Triple := (List.range (n-2)).map zeroTriangle

def zeroPedigree (n : ℕ) (hn : 3 ≤ n) : Pedigree n where
  triangles    := zeroTriangles n
  h_n          := hn
  h_length     := by simp [zeroTriangles]
  h_first      := by
    have : zeroTriangles n = (1,2,3) :: (List.range (n-3)).map (fun i => zeroTriangle (i+1)) := by
      unfold zeroTriangles
      rw [show n - 2 = (n-3) + 1 from by omega, List.range_succ_eq_map]
      simp [zeroTriangle, Function.comp]
    simp [this]
  h_layers     := by intro i hi; simp [zeroTriangles, zeroTriangle, Triple.k]
  h_in_delta   := by intro i hi; simp [zeroTriangles, zeroTriangle, mem_Delta_iff, Triple.i, Triple.j, Triple.k]
  h_distinct   := by intro i j hi hj _ _ hne; simp [zeroTriangles, zeroTriangle, Triple.i, Triple.j]; omega
  h_generators := by
    intro i hpos hi
    refine ⟨i-1, by omega, ?_⟩
    simp [zeroTriangles, zeroTriangle, List.get_eq_getElem, generators, Triple.i, Triple.j, Triple.k]
    by_cases h : i = 1
    · subst h; decide
    · simp [show i+2 > 3 from by omega]
      simp only [show i ≠ 0 from by omega, ↓reduceIte]
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by
        simp only [Prod.mk.injEq]; omega⟩

theorem hypSum_zeroPedigree (n : ℕ) (hn : 3 ≤ n) (C : Triple → ℚ) :
    hypSum C (zeroPedigree n hn) = 0 := by
  simp only [hypSum, zeroPedigree, zeroTriangles]
  have : ((List.range (n-2)).map zeroTriangle).filter (fun t => !isDefault t) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
    simp [isDefault, zeroTriangle, Triple.i, Triple.j, Triple.k]
  simp [this]

end MembershipProject.Core
