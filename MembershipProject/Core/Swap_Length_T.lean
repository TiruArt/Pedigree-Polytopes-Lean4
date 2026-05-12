-- Core/Swap/Swap_Length_T.lean
import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_PedigreeDefinition
import MembershipProject.Core.N_Discords
import MembershipProject.Core.N_Checking_Welded2_T

namespace MembershipProject.Core

lemma swap_length {n : ℕ} (P Q : Pedigree n) (C : Finset ℕ) :
    (List.ofFn (fun (i : Fin (n - 2)) =>
      let k := i.val + 3
      if k ∈ C then
        (Q.triangles.get ⟨i.val, by rw [Q.h_length]; exact i.isLt⟩)
      else
        (P.triangles.get ⟨i.val, by rw [P.h_length]; exact i.isLt⟩)
    )).length = n - 2 :=
  by simp [List.length_ofFn]

end MembershipProject.Core
