-- Core/N_Lemma_4_17.lean
-- Lemma 4.17: Singleton component swap yields valid pedigree
-- Proof follows Chapter 4, Lemma 4.17 (forsingleton)

import MembershipProject.Core.N_Swap
import MembershipProject.Core.N_Welding
import MembershipProject.Core.N_Pedigree

namespace MembershipProject.Core

open Nat Finset

def IsPedigree {n : ℕ} (P : Pedigree n) : Prop :=
  (∀ k, 3 ≤ k → k ≤ n → P.triple_at k ∈ Delta k) ∧
  P.triple_at 3 = (1, 2, 3) ∧
  (∀ k1 k2, 4 ≤ k1 → k1 < k2 → k2 ≤ n → P.triple_at k1 ≠ P.triple_at k2) ∧
  (∀ k, 4 ≤ k → k ≤ n →
    let t := P.triple_at k
    let (_, b, _) := t
    if b > 3 then P.triple_at b ∈ simple_generators t
    else P.triple_at 3 ∈ simple_generators t)

lemma singleton_swap_valid {n : ℕ} {P Q : Pedigree n} {l : ℕ}
    (h_comp : ∀ s, s ≠ l → ¬ (if s < l then welded_to P Q l s else welded_to P Q s l))
    (hl_in : l ∈ discords P Q) :
    IsPedigree (swap P Q {l}) ∧ IsPedigree (swap Q P {l}) := by
  -- Proof follows Chapter 4, Lemma 4.17
  sorry

end MembershipProject.Core
