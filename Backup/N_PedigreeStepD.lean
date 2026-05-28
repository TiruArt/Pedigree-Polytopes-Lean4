-- N_PedigreeStep.lean
import MembershipProject.Core.LearningFinsetDesirableDef
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace MembershipProject.Core

open Finset

lemma max_triple (i j k : ℕ) (hij : i < j) (hjk : j < k) :
    ({i, j, k} : Finset ℕ).max = some k := by
  apply le_antisymm
  · apply Finset.max_le; intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact WithBot.coe_le_coe.mpr (by omega)
    · exact WithBot.coe_le_coe.mpr (by omega)
    · exact le_refl _
  · exact Finset.le_max (by simp)

lemma card_triple (i j k : ℕ) (hij : i < j) (hjk : j < k) :
    ({i, j, k} : Finset ℕ).card = 3 := by
  have h2 : j ∉ ({k} : Finset ℕ) := by simp; omega
  have h3 : i ∉ ({j, k} : Finset ℕ) := by simp; omega
  rw [show ({i,j,k} : Finset ℕ) = insert i (insert j {k}) from rfl,
      Finset.card_insert_of_notMem h3,
      Finset.card_insert_of_notMem h2,
      Finset.card_singleton]

lemma le_max_of_mem {t : Finset ℕ} {m K : ℕ} (hm : t.max = some m) (hK : K ∈ t) :
    K ≤ m := by
  have h := Finset.le_max hK
  rw [hm] at h
  exact WithBot.coe_le_coe.mp h

-- All triangles in Pedigree(k-1) have max ≤ k-1
-- isPreSolution third condition: ∃ t ∈ S, (l∈t ∧ ∀x∈t, x≤l) ∧ uniqueness
-- Structure: (hlayers l hl).choose_spec = t∈S ∧ ((l∈t∧...) ∧ uniqueness)
lemma pedigree_max_lt (k : ℕ) (hk : 4 ≤ k) (S : Finset (Finset ℕ))
    (hS : Pedigree (k-1) S) (t : Finset ℕ) (ht : t ∈ S) :
    t.max.getD 0 ≤ k - 1 := by
  have htne : t.Nonempty :=
    Finset.card_pos.mp (by have := hS.1.1.2.1 t ht; omega)
  obtain ⟨m, hm⟩ := Finset.max_of_nonempty htne
  have hgetd : t.max.getD 0 = m := by rw [hm]; rfl
  rw [hgetd]
  by_contra h; push Not at h
  have hcard := hS.1.1.1
  have hlayers := hS.1.1.2.2
  -- For each l ∈ Icc 3 (k-1), get the unique triangle with max=l
  -- These are all distinct (different max values) and all ≠ t (t has max m ≥ k)
  -- Use dite function; convert with dif_pos to avoid simp issues
  let f : ℕ → Finset ℕ := fun l =>
    if hl : l ∈ Icc 3 (k-1) then (hlayers l hl).choose else ∅
  have hinj : (Icc 3 (k-1)).card ≤ (S.erase t).card := by
    apply Finset.card_le_card_of_injOn f
    · intro l hl
      -- Convert f l to (hlayers l hl).choose using dif_pos
      have hfl : f l = (hlayers l hl).choose := dif_pos hl
      rw [hfl]
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        have hcond := (hlayers l hl).choose_spec.2.1
        rw [heq] at hcond
        -- hcond.2: ∀x∈t, x≤l; applied to m (= max of t): m ≤ l
        have hml := hcond.2 m (Finset.mem_of_max hm)
        have := Finset.mem_Icc.mp hl; omega
      · exact (hlayers l hl).choose_spec.1
    · intro l1 hl1 l2 hl2 heq
      -- Convert f l1, f l2 using dif_pos
      have hfl1 : f l1 = (hlayers l1 hl1).choose := dif_pos hl1
      have hfl2 : f l2 = (hlayers l2 hl2).choose := dif_pos hl2
      rw [hfl1, hfl2] at heq
      have h1 := (hlayers l1 hl1).choose_spec
      have h2 := (hlayers l2 hl2).choose_spec
      -- heq : choose1 = choose2; use ▸ to transfer membership
      have hl12 : l2 ≤ l1 := h1.2.1.2 l2 (heq ▸ h2.2.1.1)
      have hl21 : l1 ≤ l2 := h2.2.1.2 l1 (heq.symm ▸ h1.2.1.1)
      omega
  have hce := Finset.card_erase_of_mem ht
  have hIcc : (Icc 3 (k-1)).card = k - 3 := by simp; omega
  omega

-- ============================================================
-- ZERO PEDIGREE: by decide since Decidable instance exists!
-- ============================================================

theorem zero_pedigree : Pedigree 3 {{(1:ℕ), 2, 3}} := by decide

-- ============================================================
-- INDUCTIVE STEP
-- ============================================================

theorem pedigree_extend (k i j : ℕ) (hk : 4 ≤ k)
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k)
    (S : Finset (Finset ℕ))
    (hS : Pedigree (k-1) S)
    (hedge : (j ≤ 3) ∨ (∃ tp ∈ S, tp.max = some j ∧ i ∈ tp))
    (hpair : ∀ t ∈ S, t.erase (t.max.getD 0) ≠ {i, j}) :
    Pedigree k (S ∪ {{i, j, k}}) := by
  have hmax_new := max_triple i j k hij hjk
  have hcard_new := card_triple i j k hij hjk
  have hmaxgetd : ({i,j,k} : Finset ℕ).max.getD 0 = k := by rw [hmax_new]; simp
  have herase_ijk : ({i,j,k} : Finset ℕ).erase k = {i,j} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
  have hnew : ({i,j,k} : Finset ℕ) ∉ S := by
    intro hmem
    have h1 := pedigree_max_lt k hk S hS {i,j,k} hmem
    rw [hmax_new] at h1; simp at h1; omega
  -- Prove hmax_ij and hmin_ij BEFORE unfold to avoid let-binding contamination
  have hmax_ij : ({i,j} : Finset ℕ).max.getD 0 = j := by
    have hm : ({i,j} : Finset ℕ).max = some j :=
      le_antisymm
        (Finset.max_le (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact WithBot.coe_le_coe.mpr (Nat.le_of_lt hij)
          · exact le_refl _))
        (Finset.le_max (by simp))
    rw [hm]; rfl
  have hmin_ij : ({i,j} : Finset ℕ).min.getD 0 = i := by
    have hm : ({i,j} : Finset ℕ).min = some i :=
      le_antisymm
        (Finset.min_le (by simp))
        (Finset.le_min (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact le_refl _
          · exact WithBot.coe_le_coe.mpr (Nat.le_of_lt hij)))
    rw [hm]; rfl
  -- Triangle {i,j,k} condition
  have hijk_cond : k ∈ ({i,j,k} : Finset ℕ) ∧ ∀ x ∈ ({i,j,k} : Finset ℕ), x ≤ k :=
    ⟨by simp, fun x hx => by simp at hx; omega⟩

  set K := k with hK
  constructor
  · constructor
    · constructor
      · -- card = k-2
        rw [Finset.card_union_of_disjoint (Finset.disjoint_left.mpr
          fun x hx hx' => hnew (by simp at hx'; exact hx' ▸ hx))]
        simp [hS.1.1.1]; omega
      · constructor
        · -- t.card = 3
          intro t ht
          rcases Finset.mem_union.mp ht with ht | ht
          · exact hS.1.1.2.1 t ht
          · simp only [Finset.mem_singleton] at ht; rw [ht]; exact hcard_new
        · -- unique triangle per layer
          -- isPreSolution third cond: ∃ t ∈ S∪{new}, (l∈t ∧ ∀x≤l) ∧ ∀t'∈S∪{new},...→t'=t
          intro l hl
          rw [Finset.mem_Icc] at hl
          by_cases hlk : l = K
          · subst hlk
            -- Witness: {i,j,K}
            refine ⟨{i,j,K}, Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl),
                    hijk_cond, ?_⟩
            intro t' ht'_mem ht'_cond
            rcases Finset.mem_union.mp ht'_mem with ht' | ht'
            · -- t' ∈ S: K ∈ t' but pedigree_max_lt gives max ≤ K-1
              exfalso
              have hmaxlt := pedigree_max_lt K hk S hS t' ht'
              obtain ⟨m, hm⟩ := Finset.max_of_nonempty ⟨K, ht'_cond.1⟩
              have hgetd' : t'.max.getD 0 = m := by rw [hm]; rfl
              rw [hgetd'] at hmaxlt
              have hKm := le_max_of_mem hm ht'_cond.1
              omega
            · exact Finset.mem_singleton.mp ht'
          · -- l < K: use hS
            have hl' : l ∈ Icc 3 (K-1) := Finset.mem_Icc.mpr ⟨hl.1, by omega⟩
            obtain ⟨t, ht_mem, ht_cond, ht_uniq⟩ := hS.1.1.2.2 l hl'
            refine ⟨t, Finset.mem_union_left _ ht_mem, ht_cond, ?_⟩
            intro t' ht'_mem ht'_cond
            rcases Finset.mem_union.mp ht'_mem with ht' | ht'
            · exact ht_uniq t' ht' ht'_cond
            · simp only [Finset.mem_singleton] at ht'
              exfalso; rw [ht'] at ht'_cond
              exact absurd (ht'_cond.2 K (by simp)) (by omega)
    · -- distinct pairs
      intro t1 ht1 t2 ht2
      rcases Finset.mem_union.mp ht1 with ht1 | ht1 <;>
      rcases Finset.mem_union.mp ht2 with ht2 | ht2
      · exact hS.1.2 t1 ht1 t2 ht2
      · simp only [Finset.mem_singleton] at ht2; subst ht2
        simp only [hmaxgetd, herase_ijk]
        intro _ hne; exact absurd hne (hpair t1 ht1)
      · simp only [Finset.mem_singleton] at ht1; subst ht1
        simp only [hmaxgetd, herase_ijk]
        intro _ hne; exact absurd hne.symm (hpair t2 ht2)
      · simp only [Finset.mem_singleton] at ht1 ht2; subst ht1; subst ht2; simp
  · -- generator condition
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases hS.2 t ht with hprim | ⟨tp, htp, hmax, himem⟩
      · left; exact hprim
      · right
        exact ⟨tp, Finset.mem_union_left _ htp, hmax, himem⟩
    · simp only [Finset.mem_singleton] at ht; subst ht
      simp only [hmax_new, Option.getD_some, herase_ijk, hmax_ij, hmin_ij]
      rcases hedge with hj3 | ⟨tp, htp, hmax, himem⟩
      · left
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        -- x = i or x = j; both ≤ 3 and ≥ 1 from hi, hij, hj3
        obtain h | h := hx <;> omega
      · right
        exact ⟨tp, Finset.mem_union_left _ htp, hmax, himem⟩

end MembershipProject.Core

-- ============================================================
-- USAGE: how to call pedigree_extend with hpair closed
-- In N_SelectionPedigree, the call pattern is:
--
--   let ⟨S, hS⟩ := partialPedigree k i j hk hi hij hjk
--   have hedge   := partialPedigree_hasEdge k i j hk hi hij hjk
--   have hpair   := partialPedigree_hpair k i j hk hi hij hjk
--   exact pedigree_extend k i j hk hi hij hjk S hS hedge hpair
--
-- partialPedigree_hpair closes the hpair hypothesis:
-- {i,j} is never an insertion pair in partialPedSet k i j
-- (proved by the HC construction with edge (i,j), Cases [a] and [b])
-- ============================================================
