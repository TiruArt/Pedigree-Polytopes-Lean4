-- Core/N_Decidability_T.lean
-- Decidability instances for edge_at, discords, and welded.

import MembershipProject.Core.N_Checking_Welded2_T

namespace MembershipProject.Core

-- Membership in discords is decidable
instance {n : ℕ} (P Q : Pedigree n) (q : ℕ) : Decidable (q ∈ discords P Q) := by
  simp [discords, Finset.mem_filter]; infer_instance

-- Helper: a finite range of natural numbers
private def F (q_m : ℕ) : Finset ℕ := Finset.Ico 4 q_m

-- welded is decidable because all components are decidable
instance {n : ℕ} (P Q : Pedigree n) (q_l q_m : ℕ)
    (hq_l : q_l ∈ discords P Q) (hq_m : q_m ∈ discords P Q) (hlt : q_l < q_m) :
    Decidable (welded P Q q_l q_m hq_l hq_m hlt) :=
  let a := (edge_at P q_m).1
  let b := (edge_at P q_m).2
  let c := (edge_at Q q_m).1
  let d := (edge_at Q q_m).2
  let e := (edge_at P q_l).1
  let f := (edge_at P q_l).2
  let g := (edge_at Q q_l).1
  let h := (edge_at Q q_l).2
  have h1 : Decidable (b > 3 ∧ b = q_l ∧ (g = a ∨ h = a)) := by
    have d1 : Decidable (b > 3) := infer_instance
    have d2 : Decidable (b = q_l) := infer_instance
    have d3 : Decidable (g = a) := infer_instance
    have d4 : Decidable (h = a) := infer_instance
    have d5 : Decidable (g = a ∨ h = a) := Or.decidable d3 d4
    have d6 : Decidable (b > 3 ∧ b = q_l) := And.decidable d1 d2
    exact And.decidable d6 d5
  have h2 : Decidable (d > 3 ∧ d = q_l ∧ (e = c ∨ f = c)) := by
    have d1 : Decidable (d > 3) := infer_instance
    have d2 : Decidable (d = q_l) := infer_instance
    have d3 : Decidable (e = c) := infer_instance
    have d4 : Decidable (f = c) := infer_instance
    have d5 : Decidable (e = c ∨ f = c) := Or.decidable d3 d4
    have d6 : Decidable (d > 3 ∧ d = q_l) := And.decidable d1 d2
    exact And.decidable d6 d5
  have h3 : Decidable (∃ s ∈ F q_m, edge_at Q s = (a, b)) :=
    decidable_of_iff (∃ s, s ∈ F q_m ∧ edge_at Q s = (a, b)) (by simp)
  have h4 : Decidable (∃ s ∈ F q_m, edge_at P s = (c, d)) :=
    decidable_of_iff (∃ s, s ∈ F q_m ∧ edge_at P s = (c, d)) (by simp)
  exact decidable_of_iff (welded P Q q_l q_m hq_l hq_m hlt)
    (by rw [welded]; simp [F q_m])

end MembershipProject.Core
