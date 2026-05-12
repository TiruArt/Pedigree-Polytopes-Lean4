-- Core/N_Swap.lean
-- Swap operation and restrict

import MembershipProject.Core.N_Welding
import MembershipProject.Core.N_Pedigree

namespace MembershipProject.Core

open Nat Finset

-- ============================================================
-- Swap operation: swap set C in pedigree P
-- ============================================================

def swap {n : ℕ} (P Q : Pedigree n) (C : Finset ℕ) : Pedigree n :=
  { triple_at := fun k => if k ∈ C then Q.triple_at k else P.triple_at k
    h3 := P.h3
    h_k_range := by
      intro k hk_ge hk_le
      split_ifs
      · exact Q.h_k_range k hk_ge hk_le
      · exact P.h_k_range k hk_ge hk_le
    h_base := by
      by_cases h3_in_C : 3 ∈ C
      · simp [h3_in_C]
        exact Q.h_base
      · simp [h3_in_C]
        exact P.h_base
    h_distinct := by
      sorry
    h_generator := by
      sorry }

-- ============================================================
-- Restrict pedigree to first k layers
-- ============================================================

def restrict {n : ℕ} (P : Pedigree n) (k : ℕ) (hk : 3 ≤ k ∧ k ≤ n) : Pedigree k :=
  { triple_at := P.triple_at
    h3 := hk.1
    h_k_range := by
      intro m hm hm'
      have hm_le_n : m ≤ n := by omega
      exact P.h_k_range m hm hm_le_n
    h_base := P.h_base
    h_distinct := by
      intro m1 m2 hm1 hm12 hm2
      have hm1' : 4 ≤ m1 := by omega
      have hm2' : m2 ≤ n := by omega
      exact P.h_distinct m1 m2 hm1' hm12 hm2'
    h_generator := by
      intro m hm_ge hm_le
      have hm_ge' : 4 ≤ m := by omega
      have hm_le_n : m ≤ n := by omega
      have h_gen := P.h_generator m hm_ge' hm_le_n
      -- Need to show that restrict preserves generator property
      sorry }

end MembershipProject.Core
