import MembershipProject.Core.N_Basic
import MembershipProject.Core.N_PedigreeDefinition
import MembershipProject.Core.N_Discords
import MembershipProject.Core.N_Checking_Welded2_T

namespace MembershipProject.Core

lemma swap_first {n : ℕ} (P Q : Pedigree n) (C : Finset ℕ)
    (h_sub : C ⊆ discords P Q) :
    let R_triangles := List.ofFn (fun (i : Fin (n - 2)) =>
      let k := i.val + 3
      if k ∈ C then
        (Q.triangles.get ⟨i.val, by rw [Q.h_length]; exact i.isLt⟩)
      else
        (P.triangles.get ⟨i.val, by rw [P.h_length]; exact i.isLt⟩)
    )
    R_triangles.head? = some (1, 2, 3) :=
  by
    have h3_notin_C : 3 ∉ C := by
      intro h
      have h3_disc : 3 ∈ discords P Q := h_sub h
      simp [discords, Finset.mem_Ico] at h3_disc
      contradiction
    have h_len_pos : 0 < n - 2 := by
      have h_n_ge_3 : n ≥ 3 := P.h_n
      exact Nat.sub_pos_of_lt h_n_ge_3
    -- Prove that the first element of the list is (1,2,3)
    have h_first_elem : (List.ofFn (fun (i : Fin (n - 2)) =>
      let k := i.val + 3
      if k ∈ C then Q.triangles.get ⟨i.val, by rw [Q.h_length]; exact i.isLt⟩
      else P.triangles.get ⟨i.val, by rw [P.h_length]; exact i.isLt⟩
    )).get 0 = (1, 2, 3) := by
      simp [List.get_ofFn, Fin.val_zero, if_neg h3_notin_C]
      -- Now we need P.triangles[0] = (1,2,3)
      have h_P0 : P.triangles[0] = (1, 2, 3) := by
        cases P.triangles with
        | nil => contradiction
        | cons x xs =>
          have h_head := P.h_first
          simp [List.head?] at h_head
          rw [h_head]
          rfl
      exact h_P0
    -- For a non-empty list, head? = some (get 0)
    have h_nonempty : (List.ofFn (fun (i : Fin (n - 2)) =>
      let k := i.val + 3
      if k ∈ C then Q.triangles.get ⟨i.val, by rw [Q.h_length]; exact i.isLt⟩
      else P.triangles.get ⟨i.val, by rw [P.h_length]; exact i.isLt⟩
    )) ≠ [] := by
      rw [List.length_eq_zero]
      simp [List.length_ofFn]
      omega
    rw [List.head?_eq_some_iff]
    exact ⟨h_nonempty, h_first_elem⟩

end MembershipProject.Core
