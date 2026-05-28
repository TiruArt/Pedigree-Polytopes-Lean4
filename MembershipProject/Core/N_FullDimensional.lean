-- Core/N_FullDimensional.lean
-- Theorem fullDimensional_An (Chapter 7, Arthanari 2023):
-- conv(A_n) is full dimensional: dim(conv(A_n)) = alpha_n.
--
-- Proof by contradiction (book proof):
-- Suppose dim(conv(A_n)) < alpha_n. Then there exists a non-trivial
-- hyperplane CY = c_0 containing all pedigrees Y in A_n.
-- allCoeffsZero proves: c_0 = 0 AND every non-default coefficient C(i,j,k+1) = 0.
-- So the hyperplane is trivial (C = 0, c_0 = 0) -- contradiction.
-- Therefore dim(conv(A_n)) = alpha_n.
--
-- Structure:
-- Step 1 (Claim 1): c_0 = 0 via zeroPedigree.
-- Step 2 (Claim 2): c_4 = 0 via claim2 (N_Claim2Pedigree.lean).
-- Step 3 (Induction): C(i,j,k+1) = 0 for all k>=4 via coeff_zero (N_SelectionPedigree.lean).
-- allCoeffsZero: combines Steps 1-3.
-- fullDimensional_An: the trivial hyperplane is the only one satisfied by all of A_n.
--
-- Reference: Arthanari, T.S. Pedigree Polytopes, Springer Nature 2023, Chapter 7.

import MembershipProject.Core.N_ZeroPedigree
import MembershipProject.Core.N_Claim2Pedigree
import MembershipProject.Core.N_SelectionPedigree
import Mathlib.Tactic

namespace MembershipProject.Core

set_option linter.unusedVariables false

/-- allCoeffsZero: any hyperplane CY = c_0 satisfied by all pedigrees in A_n
    must have c_0 = 0 and all non-default coefficients C(i,j,k+1) = 0.
    Proof:
    - c_0 = 0: zeroPedigree gives Y = 0, so CY = 0 = c_0.
    - C(i,j,k+1) = 0: strong induction on k.
      Base k=4: claim2 (N_Claim2Pedigree.lean).
      Step k≥5: coeff_zero (N_SelectionPedigree.lean) — uses three selection
      pedigrees giving equations (e1),(e2),(e3),(e4) from the book proof. -/
theorem allCoeffsZero (n : ℕ) (hn : 6 ≤ n)
    (C : Triple → ℚ) (c₀ : ℚ)
    (hC : ∀ P : Pedigree n, hypSum C P = c₀) :
    c₀ = 0 ∧
    ∀ (k i j : ℕ), 4 ≤ k → k + 2 ≤ n → 1 ≤ i → i < j → j < k →
      isDefault (i,j,k+1) = false → C (i,j,k+1) = 0 := by
  -- Step 1: c_0 = 0
  have hc0 : c₀ = 0 := by
    have h := hC (zeroPedigree n (by omega))
    rw [hypSum_zeroPedigree] at h; linarith
  have hC' : ∀ P : Pedigree n, hypSum C P = 0 :=
    fun P => by rw [← hc0]; exact hC P
  refine ⟨hc0, ?_⟩
  -- Prove by strong induction on k: C(i,j,k+1) = 0
  -- This exactly matches coeff_zero's conclusion.
  -- coeff_zero's ih asks for C(a,b,m) = 0 for m ≤ k.
  -- We provide this from our strong induction: for m ≤ k,
  -- apply ih at m-1 (< k) to get C(a,b,(m-1)+1) = C(a,b,m) = 0,
  -- handling m=4 with claim2.
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro i j hk4 hkn hi hij hjk hnd
    -- The ih_bridge converts our ih to coeff_zero's ih format
    -- ih_bridge: prove C(a,b,m) = 0 for m ≤ k
    -- Use revert trick: intro all vars, revert a b and hypotheses, induct on m,
    -- re-intro so ihm quantifies over ALL a,b
    have ih_bridge : ∀ m a b, 1 ≤ a → a < b → b < m → 4 ≤ m → m ≤ k →
        isDefault (a,b,m) = false → C (a,b,m) = 0 := by
      intro m a b ha hab hbm hm4 hmt hndm
      revert a b ha hab hbm hm4 hmt hndm
      induction m using Nat.strongRecOn with
      | ind m ihm =>
        -- ihm : ∀ m' < m, ∀ a b, 1≤a → a<b → b<m' → 4≤m' → m'≤k →
        --         isDefault(a,b,m')=false → C(a,b,m') = 0
        intro a b ha hab hbm hm4 hmt hndm
        by_cases hm4' : m = 4
        · subst hm4'
          have hc := claim2 n hn C hC'
          have ha2 : a ≤ 2 := by omega
          have hb3 : b ≤ 3 := by omega
          interval_cases a <;> interval_cases b <;>
            simp_all [isDefault, Triple.i, Triple.j, Triple.k]
        · have hm5 : 5 ≤ m := by omega
          have hm1_eq : m - 1 + 1 = m := by omega
          rcases Nat.lt_or_ge b (m-1) with hblt | hbge
          · -- b < m-1: apply outer ih at m-1
            have hndm' : isDefault (a, b, m-1+1) = false := hm1_eq ▸ hndm
            have := ih (m-1) (by omega) a b (by omega) (by omega) ha hab hblt hndm'
            rwa [hm1_eq] at this
          · -- b = m-1: use m = m' + 1 to avoid Nat subtraction
            -- C(a, m-1, m) = 0 via selectionPedigree2 and selectionPedigree3
            have hbeq : b = m - 1 := by omega
            subst hbeq
            -- Write m = m' + 1 to avoid m-1 subtraction issues
            obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
            subst hm'
            -- Now goal: C(a, m', m'+1) = 0
            -- selectionPedigree2 n m' a: gives C(a,m',m'+1) + C(a,m'+1,m'+2) = 0
            -- selectionPedigree3 n m' a: gives C(a,m'+1,m'+2) = 0
            have hm'4 : 4 ≤ m' := by omega
            have hm'n1 : m' + 1 ≤ n := by omega
            have hm'n2 : m' + 2 ≤ n := by omega
            -- Build ih for selectionPedigree2/3:
            -- needs C(a',b',l) = 0 for l ≤ m'
            -- ihm : ∀ l < m'+1, ... → C(a',b',l) = 0
            -- so ihm l (by omega : l < m'+1) gives what we need
            -- ih for selectionPedigree2/3: C(a',b',l) = 0 for l ≤ m'
            -- ihm from Nat.strongRecOn: ihm l (hlt : l < m'+1) ...
            -- ihm : ∀ l, l < m'+1 → ... → C(a',b',l) = 0
            -- need l < m'+1 from hlt : l ≤ m'
            -- ihm : ∀ l, m'+1-1 < l → 4 ≤ l → l ≤ k → isDefault(a, m'+1-1, l) = false → C(a,m'+1-1,l) = 0
            -- b = m'+1-1 = m' in this context
            -- rewrite m'+1-1 = m' to avoid Nat subtraction confusion
            have hm'_eq : m' + 1 - 1 = m' := by omega
            -- hm'_ih: directly use ihm since l < m'+1 (from hlt: l ≤ m')
            -- ihm : ∀ m < m'+1, ∀ a b, 1≤a → a<b → b<m → 4≤m → m≤k → ... → C(a,b,m) = 0
            have hm'_ih : ∀ a' b' l, 1 ≤ a' → a' < b' → b' < l → 4 ≤ l → l ≤ m' →
                isDefault (a',b',l) = false → C (a',b',l) = 0 :=
              fun a' b' l ha' hab' hb'l hl4 hlt hndl =>
                ihm l (by omega) a' b' ha' hab' hb'l hl4 (by omega) hndl
            -- hnd_am' is exactly hndm after rewriting (no proof needed)
            have hnd_am' : isDefault (a, m', m'+1) = false := hndm
            -- hnd_am'2: isDefault(a, m'+1, m'+2) = (a+2 == m'+2 && true)
            -- need a+2 ≠ m'+2, follows from hail : a < m'
            have hail : a < m' := hab
            have hnd_am'2 : isDefault (a, m'+1, m'+2) = false := by
              simp [isDefault, Triple.i, Triple.j, Triple.k]; omega
            have hP2 := hC' (selectionPedigree2 n m' a hn hm'4 hm'n1 ha hail)
            have hP3 := hC' (selectionPedigree3 n m' a hn hm'4 hm'n2 ha hail)
            rw [hypSum_P2 n m' a hn hm'4 hm'n1 ha hail hnd_am' C hm'_ih] at hP2
            rw [hypSum_P3 n m' a hn hm'4 hm'n2 ha hail hnd_am' hnd_am'2 C hm'_ih] at hP3
            rw [hm'_eq]; exact hP2
    -- Now apply coeff_zero with ih_bridge (reorder args: m first)
    exact coeff_zero n k i j hn hk4 hkn hi hij hjk hnd C hC'
      (fun a b m ha hab hbm hm4 hmt hndm => ih_bridge m a b ha hab hbm hm4 hmt hndm)

/-- fullDimensional_An (Chapter 7, Arthanari 2023):
    The trivial hyperplane (C = 0, c_0 = 0) is the ONLY hyperplane
    satisfied by all members of A_n.
    Equivalently: conv(A_n) is full dimensional — dim(conv(A_n)) = alpha_n.

    Proof: allCoeffsZero shows any hyperplane CY = c_0 containing all
    pedigrees must have c_0 = 0 and C(i,j,k) = 0 for all non-default (i,j,k).
    So C = 0 and c_0 = 0 — the hyperplane is trivial.
    No proper hyperplane contains all of A_n → dim(conv(A_n)) = alpha_n. -/
theorem fullDimensional_An (n : ℕ) (hn : 6 ≤ n)
    (C : Triple → ℚ) (c₀ : ℚ)
    (hC : ∀ P : Pedigree n, hypSum C P = c₀) :
    c₀ = 0 ∧ ∀ (k i j : ℕ), 4 ≤ k → k + 2 ≤ n → 1 ≤ i → i < j → j < k →
      isDefault (i,j,k+1) = false → C (i,j,k+1) = 0 :=
  allCoeffsZero n hn C c₀ hC

end MembershipProject.Core
