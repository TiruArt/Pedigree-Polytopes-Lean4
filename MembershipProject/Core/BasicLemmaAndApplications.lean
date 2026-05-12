import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic

/-!
# Basic Lemma for Pedigree Polytope Study

This file contains a formalization and proof of the Basic Lemma used in
pedigree polytope theory.
-/

open Finset

/-- A partition of a finite set -/
structure Partition (D : Type*) [DecidableEq D] [Fintype D] where
  blocks : Finset (Finset D)
  nonempty_blocks : ∀ B ∈ blocks, B.Nonempty
  disjoint : ∀ B₁ ∈ blocks, ∀ B₂ ∈ blocks, B₁ ≠ B₂ → Disjoint B₁ B₂
  covers_unique : ∀ d : D, ∃! B, B ∈ blocks ∧ d ∈ B
  covers_all : univ ⊆ blocks.biUnion id

/-- An additive nonnegative function on finite sets -/
structure AdditiveFunction (D : Type*) [DecidableEq D] where
  g : Finset D → ℝ
  nonneg : ∀ S, 0 ≤ g S
  empty_zero : g ∅ = 0
  additive : ∀ S T, Disjoint S T → g (S ∪ T) = g S + g T

/-- A transportation problem -/
structure TransportationProblem where
  n₁ : ℕ
  n₂ : ℕ
  supply : Fin n₁ → ℝ
  demand : Fin n₂ → ℝ
  arcs : Finset (Fin n₁ × Fin n₂)

/-- A flow is feasible if it satisfies all constraints -/
def FeasibleFlow (tp : TransportationProblem) (f : Fin tp.n₁ → Fin tp.n₂ → ℝ) : Prop :=
  (∀ i j, 0 ≤ f i j) ∧
  (∀ i j, (i, j) ∉ tp.arcs → f i j = 0) ∧
  (∀ i, (univ.sum fun j => f i j) = tp.supply i) ∧
  (∀ j, (univ.sum fun i => f i j) = tp.demand j)

/-- Additivity extends to finite unions of pairwise disjoint sets -/
lemma additive_biUnion {D : Type*} [DecidableEq D] (af : AdditiveFunction D)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Finset D)
    (h_disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) :
    af.g (s.biUnion f) = s.sum (fun i => af.g (f i)) := by
  induction s using Finset.induction with
  | empty =>
    simp only [biUnion_empty, sum_empty]
    exact af.empty_zero
  | insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha]
    have disj : Disjoint (f a) (s.biUnion f) := by
      intro x
      simp only [mem_inter, mem_biUnion]
      intro hxa ⟨i, hi, hxi⟩
      exact (h_disj a (mem_insert_self a s) i (mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))).le_bot ⟨hxa, hxi⟩
    rw [af.additive (f a) (s.biUnion f) disj]
    congr 1
    apply ih
    intros i hi j hj hij
    exact h_disj i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij

/-- For a fixed block B, the union of B ∩ C over all blocks C in a partition equals B -/
lemma union_intersections_eq {D : Type*} [DecidableEq D] [Fintype D]
    (P : Partition D) (B : Finset D) :
    B = P.blocks.biUnion (fun C => B ∩ C) := by
  ext d
  constructor
  · intro hd
    simp only [mem_biUnion]
    have ⟨C, ⟨hC, hdC⟩, _⟩ := P.covers_unique d
    exact ⟨C, hC, mem_inter.mpr ⟨hd, hdC⟩⟩
  · intro h
    simp only [mem_biUnion] at h
    obtain ⟨C, _, hd⟩ := h
    exact mem_inter.mp hd |>.1

/-- Intersections of a set with partition blocks are pairwise disjoint -/
lemma inter_partition_disjoint {D : Type*} [DecidableEq D]
    (P : Partition D) (B : Finset D) :
    ∀ C₁ ∈ P.blocks, ∀ C₂ ∈ P.blocks, C₁ ≠ C₂ → Disjoint (B ∩ C₁) (B ∩ C₂) := by
  intros C₁ hC₁ C₂ hC₂ hne
  intro d
  simp only [mem_inter, mem_inter]
  intro ⟨_, hd_C₁⟩ ⟨_, hd_C₂⟩
  exact (P.disjoint C₁ hC₁ C₂ hC₂ hne).le_bot ⟨hd_C₁, hd_C₂⟩

/-- Main technical lemma: g(B) = Σ g(B ∩ C) for C in partition P -/
lemma sum_intersection_parts {D : Type*} [DecidableEq D] [Fintype D]
    (af : AdditiveFunction D) (P : Partition D) (B : Finset D) :
    af.g B = P.blocks.sum (fun C => af.g (B ∩ C)) := by
  have h_union := union_intersections_eq P B

  let nonempty_inters := P.blocks.filter (fun C => (B ∩ C).Nonempty)

  have h_biUnion_filter : P.blocks.biUnion (fun C => B ∩ C) =
                           nonempty_inters.biUnion (fun C => B ∩ C) := by
    ext d
    simp only [mem_biUnion, nonempty_inters, mem_filter]
    constructor
    · intro ⟨C, hC, hd⟩
      exact ⟨C, ⟨hC, ⟨d, hd⟩⟩, hd⟩
    · intro ⟨C, ⟨hC, _⟩, hd⟩
      exact ⟨C, hC, hd⟩

  rw [h_union, h_biUnion_filter]

  rw [additive_biUnion af nonempty_inters (fun C => B ∩ C)]
  · have key : nonempty_inters.sum (fun C => af.g (B ∩ C)) =
               P.blocks.sum (fun C => af.g (B ∩ C)) := by
      rw [← sum_filter_add_sum_filter_not P.blocks (fun C => (B ∩ C).Nonempty)]
      simp only [nonempty_inters]
      congr 1
      apply sum_eq_zero
      intros C hC
      simp only [mem_filter, not_and] at hC
      have : ¬(B ∩ C).Nonempty := hC.2 hC.1
      rw [not_nonempty_iff_eq_empty.mp this, af.empty_zero]
    rw [key]
  · intros C₁ hC₁ C₂ hC₂ hne
    simp only [nonempty_inters, mem_filter] at hC₁ hC₂
    exact inter_partition_disjoint P B C₁ hC₁.1 C₂ hC₂.1 hne

/-- Construct an enumeration of partition blocks -/
noncomputable def enumerate_blocks {D : Type*} [DecidableEq D] [Fintype D] (P : Partition D) :
    Σ (n : ℕ), { enum : Fin n → Finset D //
      (∀ i, enum i ∈ P.blocks) ∧
      (∀ B ∈ P.blocks, ∃ i, enum i = B) ∧
      (∀ i j, enum i = enum j → i = j) } := by
  classical
  let n := P.blocks.card
  let equiv := P.blocks.equivFin
  use n
  use fun i => equiv.symm (Fin.cast (by rfl : n = P.blocks.card) i)
  constructor
  · intro i
    exact (equiv.symm _).2
  constructor
  · intros B hB
    use Fin.cast (by rfl : P.blocks.card = n) (equiv ⟨B, hB⟩)
    simp only [Fin.cast_trans, Fin.cast_eq_self, Equiv.symm_apply_apply]
  · intros i j h_eq
    apply Fin.ext
    apply equiv.symm.injective
    ext
    exact h_eq

/-- Helper lemma for summing over enumerations -/
lemma sum_image_enum {D : Type*} [DecidableEq D] [Fintype D]
    (n : ℕ) (enum : Fin n → Finset D) (P : Finset (Finset D))
    (h_mem : ∀ i, enum i ∈ P)
    (h_surj : ∀ B ∈ P, ∃ i, enum i = B)
    (h_inj : ∀ i j, enum i = enum j → i = j)
    (h_card : P.card = n)
    (f : Finset D → ℝ) :
    univ.sum (fun i => f (enum i)) = P.sum f := by
  rw [← sum_image h_inj]
  congr 1
  ext B
  simp only [mem_image, mem_univ, true_and]
  constructor
  · intro ⟨i, rfl⟩
    exact h_mem i
  · intro hB
    obtain ⟨i, rfl⟩ := h_surj B hB
    exact ⟨i, rfl⟩

/-- The Basic Lemma with explicit enumerations -/
theorem basic_lemma_with_enum {D : Type*} [DecidableEq D] [Fintype D]
    (af : AdditiveFunction D) (P₁ P₂ : Partition D)
    (n₁ n₂ : ℕ) (enum₁ : Fin n₁ → Finset D) (enum₂ : Fin n₂ → Finset D)
    (h₁_mem : ∀ i, enum₁ i ∈ P₁.blocks)
    (h₂_mem : ∀ j, enum₂ j ∈ P₂.blocks)
    (h₁_surj : ∀ B ∈ P₁.blocks, ∃ i, enum₁ i = B)
    (h₂_surj : ∀ B ∈ P₂.blocks, ∃ j, enum₂ j = B)
    (h₁_inj : ∀ i j, enum₁ i = enum₁ j → i = j)
    (h₂_inj : ∀ i j, enum₂ i = enum₂ j → i = j)
    (h₁_card : P₁.blocks.card = n₁)
    (h₂_card : P₂.blocks.card = n₂) :
    let tp : TransportationProblem := {
      n₁ := n₁
      n₂ := n₂
      supply := fun i => af.g (enum₁ i)
      demand := fun j => af.g (enum₂ j)
      arcs := univ.filter (fun (i, j) => (enum₁ i ∩ enum₂ j).Nonempty)
    }
    let f := fun i j => af.g (enum₁ i ∩ enum₂ j)
    FeasibleFlow tp f := by
  intro tp f
  constructor
  · -- Nonnegativity
    intros i j
    exact af.nonneg (enum₁ i ∩ enum₂ j)
  constructor
  · -- Zero flow on non-arcs
    intros i j h_not_arc
    simp only [tp, mem_filter, mem_univ, true_and] at h_not_arc
    have : enum₁ i ∩ enum₂ j = ∅ := not_nonempty_iff_eq_empty.mp h_not_arc
    simp only [f, this, af.empty_zero]
  constructor
  · -- Supply constraints
    intro i
    simp only [tp]
    calc univ.sum (fun j => f i j)
        = univ.sum (fun j => af.g (enum₁ i ∩ enum₂ j)) := by rfl
      _ = P₂.blocks.sum (fun C => af.g (enum₁ i ∩ C)) :=
            sum_image_enum n₂ enum₂ P₂.blocks h₂_mem h₂_surj h₂_inj h₂_card _
      _ = af.g (enum₁ i) := (sum_intersection_parts af P₂ (enum₁ i)).symm
  · -- Demand constraints
    intro j
    simp only [tp]
    calc univ.sum (fun i => f i j)
        = univ.sum (fun i => af.g (enum₁ i ∩ enum₂ j)) := by rfl
      _ = P₁.blocks.sum (fun B => af.g (B ∩ enum₂ j)) :=
            sum_image_enum n₁ enum₁ P₁.blocks h₁_mem h₁_surj h₁_inj h₁_card _
      _ = af.g (enum₂ j) := (sum_intersection_parts af P₁ (enum₂ j)).symm

/-- The Basic Lemma: intersection-based allocation is feasible -/
theorem basic_lemma {D : Type*} [DecidableEq D] [Fintype D]
    (D_nonempty : (univ : Finset D).Nonempty)
    (af : AdditiveFunction D)
    (P₁ P₂ : Partition D) :
    ∃ (n₁ n₂ : ℕ) (enum₁ : Fin n₁ → Finset D) (enum₂ : Fin n₂ → Finset D)
      (h₁ : ∀ i, enum₁ i ∈ P₁.blocks) (h₂ : ∀ j, enum₂ j ∈ P₂.blocks),
    let tp : TransportationProblem := {
      n₁ := n₁
      n₂ := n₂
      supply := fun i => af.g (enum₁ i)
      demand := fun j => af.g (enum₂ j)
      arcs := univ.filter (fun (i, j) => (enum₁ i ∩ enum₂ j).Nonempty)
    }
    let f := fun i j => af.g (enum₁ i ∩ enum₂ j)
    FeasibleFlow tp f := by
  obtain ⟨n₁, enum₁, h₁_mem, h₁_surj, h₁_inj⟩ := enumerate_blocks P₁
  obtain ⟨n₂, enum₂, h₂_mem, h₂_surj, h₂_inj⟩ := enumerate_blocks P₂

  refine ⟨n₁, n₂, enum₁, enum₂, h₁_mem, h₂_mem, ?_⟩

  exact basic_lemma_with_enum af P₁ P₂ n₁ n₂ enum₁ enum₂
    h₁_mem h₂_mem h₁_surj h₂_surj h₁_inj h₂_inj rfl rfl
