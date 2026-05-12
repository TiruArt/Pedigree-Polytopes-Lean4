-- N_FullDimensional.lean
import MembershipProject.Core.N_ZeroPedigree
import MembershipProject.Core.N_Claim2Pedigree
import MembershipProject.Core.N_SelectionPedigree
import Mathlib.Tactic

namespace MembershipProject.Core

set_option linter.unusedVariables false

theorem allCoeffsZero (n : ℕ) (hn : 6 ≤ n)
    (C : Triple → ℚ) (c₀ : ℚ)
    (hC : ∀ P : Pedigree n, hypSum C P = c₀) :
    c₀ = 0 ∧
    ∀ (k i j : ℕ), 4 ≤ k → k ≤ n → 1 ≤ i → i < j → j < k →
      isDefault (i,j,k) = false → C (i,j,k) = 0 := by
  have hc0 : c₀ = 0 := by
    have h := hC (zeroPedigree n (by omega))
    rw [hypSum_zeroPedigree] at h; linarith
  have hC' : ∀ P : Pedigree n, hypSum C P = 0 :=
    fun P => by rw [← hc0]; exact hC P
  refine ⟨hc0, ?_⟩
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro i j hk4 hkn hi hij hjk hnd
    by_cases hk4' : k = 4
    · -- BASE k=4: 1 ≤ i < j < 4, so (i,j) ∈ {(1,2),(1,3),(2,3)}
      subst hk4'
      have hc := claim2 n hn C hC'
      -- i ∈ {1,2}, j ∈ {i+1,...,3}
      have hi3 : i ≤ 2 := by omega
      have hj3 : j ≤ 3 := by omega
      interval_cases i <;> interval_cases j <;>
        simp_all [isDefault, Triple.i, Triple.j, Triple.k]
    · exact coeff_zero n k i j hn hk4 hkn hi hij hjk hnd C hC'
        (fun a b m ha hab hbm hm4 hmt hmn hndm =>
          ih m hmt a b hm4 hmn ha hab hbm hndm)

end MembershipProject.Core
