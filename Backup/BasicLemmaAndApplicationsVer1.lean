import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# Basic Lemma for Pedigree Polytope Study - Minimal Import Version
-/

open Finset

variable {D : Type*} [DecidableEq D] [Fintype D]

/-- An additive nonnegative function on finite sets -/
structure AdditiveFunction where
  g : Finset D → ℝ
  nonneg : ∀ S, 0 ≤ g S
  empty_zero : g ∅ = 0
  additive : ∀ S T, Disjoint S T → g (S ∪ T) = g S + g T

/-- Helper for summing over finset -/
noncomputable def finset_sum {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  (s.1.map f).sum

notation "∑" x " in " s ", " f:60 => finset_sum s (fun x => f)

/-- A partition of a finite set -/
structure Partition where
  blocks : Finset (Finset D)
  nonempty_blocks : ∀ B ∈ blocks, B.Nonempty
  disjoint : ∀ B₁ ∈ blocks, ∀ B₂ ∈ blocks, B₁ ≠ B₂ → Disjoint B₁ B₂
  covers : ∀ d : D, ∃ B ∈ blocks, d ∈ B
  unique : ∀ d : D, ∀ B₁ ∈ blocks, ∀ B₂ ∈ blocks, d ∈ B₁ → d ∈ B₂ → B₁ = B₂

namespace AdditiveFunction

variable (af : AdditiveFunction)

/-- Additivity extends to finite disjoint unions -/
theorem additive_biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Finset D)
    (h_disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) :
    af.g (s.biUnion f) = ∑ i in s, af.g (f i) := by
  classical
  induction' s using Finset.induction_on with a s has ih
  · simp [af.empty_zero]
  · rw [biUnion_insert]
    have : ∑ i in insert a s, af.g (f i) = af.g (f a) + ∑ i in s, af.g (f i) := by
      simp [has]
    rw [this, ← ih]
    · have disj : Disjoint (f a) (s.biUnion f) := by
        intro x hx
        simp only [mem_inter, mem_biUnion] at hx
        rcases hx with ⟨hxa, ⟨i, hi, hxi⟩⟩
        exact (h_disj a (mem_insert_self a s) i (mem_insert_of_mem hi)
          (fun h => has (h ▸ hi))).le_bot ⟨hxa, hxi⟩
      rw [af.additive _ _ disj]
    · intro i hi j hj hij
      exact h_disj i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij

end AdditiveFunction

/-- Main technical lemma: g(B) = Σ g(B ∩ C) for C in partition P -/
theorem sum_intersection_parts (af : AdditiveFunction) (P : Partition) (B : Finset D) :
    af.g B = ∑ C in P.blocks, af.g (B ∩ C) := by
  classical
  have h_disj : ∀ C₁ ∈ P.blocks, ∀ C₂ ∈ P.blocks, C₁ ≠ C₂ → Disjoint (B ∩ C₁) (B ∩ C₂) := by
    intro C₁ hC₁ C₂ hC₂ hne
    have := P.disjoint C₁ hC₁ C₂ hC₂ hne
    exact Finset.disjoint_inter_inter_left _ _ this

  have h_union : B = P.blocks.biUnion (fun C => B ∩ C) := by
    ext x
    constructor
    · intro hx
      rcases P.covers x with ⟨C, hC, hxC⟩
      exact mem_biUnion.mpr ⟨C, hC, mem_inter.mpr ⟨hx, hxC⟩⟩
    · intro hx
      rcases mem_biUnion.mp hx with ⟨C, _, hxC⟩
      exact (mem_inter.mp hxC).left

  rw [h_union]
  exact af.additive_biUnion P.blocks (fun C => B ∩ C) h_disj

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
  (∀ i, ∑ j : Fin tp.n₂, f i j = tp.supply i) ∧
  (∀ j, ∑ i : Fin tp.n₁, f i j = tp.demand j)

/-- Helper: sum over Fin n -/
noncomputable def sum_fin {n : ℕ} (f : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, f i

/-- The Basic Lemma: intersection-based flow is feasible -/
theorem basic_lemma (af : AdditiveFunction) (P₁ P₂ : Partition) :
    ∃ (tp : TransportationProblem) (f : Fin tp.n₁ → Fin tp.n₂ → ℝ), FeasibleFlow tp f := by
  classical
  -- Use the actual blocks as our enumeration
  let blocks₁ := P₁.blocks
  let blocks₂ := P₂.blocks

  -- Convert to arrays for indexing
  let arr₁ : Array (Finset D) := blocks₁.toArray
  let arr₂ : Array (Finset D) := blocks₂.toArray

  let n₁ := arr₁.size
  let n₂ := arr₂.size

  -- Define enumerations
  let enum₁ : Fin n₁ → Finset D := fun i => arr₁.get ⟨i.val, i.is_lt⟩
  let enum₂ : Fin n₂ → Finset D := fun j => arr₂.get ⟨j.val, j.is_lt⟩

  -- Define transportation problem
  let tp : TransportationProblem := {
    n₁ := n₁
    n₂ := n₂
    supply := fun i => af.g (enum₁ i)
    demand := fun j => af.g (enum₂ j)
    arcs := univ  -- All pairs connected
  }

  -- Define intersection-based flow
  let f : Fin tp.n₁ → Fin tp.n₂ → ℝ :=
    fun i j => af.g (enum₁ i ∩ enum₂ j)

  refine ⟨tp, f, ?_⟩

  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    exact af.nonneg _
  · intro i j h
    simp [tp] at h
  · intro i
    have : ∑ j : Fin n₂, f i j = ∑ C in P₂.blocks, af.g (enum₁ i ∩ C) := by
      simp [f, sum_fin]
      -- Show the sum over Fin n₂ equals sum over blocks₂
      apply Finset.sum_bij (fun (j : Fin n₂) _ => enum₂ j) ?_ ?_ ?_ ?_
      · intro j hj
        simp [hj, enum₂]
        have : enum₂ j ∈ blocks₂ := by
          simp [enum₂, arr₂]
          exact Array.get_mem _ _ _
        simp [this]
      · intro j hj
        simp
      · intro j₁ j₂ hj₁ hj₂ h
        simp [enum₂] at h ⊢
        exact h
      · intro C hC
        have : C ∈ arr₂ := by
          simpa [arr₂] using hC
        rcases Array.mem_iff_get.1 this with ⟨idx, hidx, hC'⟩
        refine ⟨⟨idx, by simp [hidx, n₂]⟩, by simp, ?_⟩
        simp [enum₂, hC']
    rw [this, sum_intersection_parts af P₂ (enum₁ i)]
  · intro j
    have : ∑ i : Fin n₁, f i j = ∑ B in P₁.blocks, af.g (B ∩ enum₂ j) := by
      simp [f, sum_fin]
      -- Show the sum over Fin n₁ equals sum over blocks₁
      apply Finset.sum_bij (fun (i : Fin n₁) _ => enum₁ i) ?_ ?_ ?_ ?_
      · intro i hi
        simp [hi, enum₁]
        have : enum₁ i ∈ blocks₁ := by
          simp [enum₁, arr₁]
          exact Array.get_mem _ _ _
        simp [this]
      · intro i hi
        simp
      · intro i₁ i₂ hi₁ hi₂ h
        simp [enum₁] at h ⊢
        exact h
      · intro B hB
        have : B ∈ arr₁ := by
          simpa [arr₁] using hB
        rcases Array.mem_iff_get.1 this with ⟨idx, hidx, hB'⟩
        refine ⟨⟨idx, by simp [hidx, n₁]⟩, by simp, ?_⟩
        simp [enum₁, hB']
    rw [this, sum_intersection_parts af P₁ (enum₂ j)]
