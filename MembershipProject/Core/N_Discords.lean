-- Core/N_Discords.lean
-- Discord and adjacency. Chapter 4, Pedigree Polytopes (Arthanari, Springer Nature 2023).

import MembershipProject.Core.N_PedigreeDefinition

namespace MembershipProject.Core

set_option linter.unusedVariables false

instance {n : ℕ} : DecidableEq (Pedigree n) := fun P Q =>
  if h : P.triangles = Q.triangles then isTrue (Pedigree.ext h)
  else isFalse (fun heq => h (congr_arg Pedigree.triangles heq))

-- ============================================================================
-- CHAR_VEC
-- ============================================================================

def char_vec {n : ℕ} (P : Pedigree n) : LayeredPoint n :=
  fun t => if t ∈ P.triangles then 1 else 0

@[simp] lemma char_vec_mem {n : ℕ} (P : Pedigree n) (t : Triple)
    (h : t ∈ P.triangles) : char_vec P t = 1 := by simp [char_vec, h]

@[simp] lemma char_vec_not_mem {n : ℕ} (P : Pedigree n) (t : Triple)
    (h : t ∉ P.triangles) : char_vec P t = 0 := by simp [char_vec, h]

lemma char_vec_01 {n : ℕ} (P : Pedigree n) (t : Triple) :
    char_vec P t = 0 ∨ char_vec P t = 1 := by
  simp [char_vec]; by_cases h : t ∈ P.triangles <;> simp [h]

-- ============================================================================
-- EDGE AT LAYER
-- ============================================================================

def edge_at {n : ℕ} (P : Pedigree n) (k : ℕ) : ℕ × ℕ :=
  if h : k - 3 < P.triangles.length then
    ((P.triangles.get ⟨k-3, h⟩).i, (P.triangles.get ⟨k-3, h⟩).j)
  else (0, 0)

-- ============================================================================
-- TRIPLE IN DELTA / SAME EDGE SAME TRIPLE
-- ============================================================================

private lemma triple_in_Delta {n : ℕ} (P : Pedigree n)
    (l : ℕ) (hl3 : 3 ≤ l) (hln : l ≤ n) (hidx : l-3 < P.triangles.length) :
    P.triangles.get ⟨l-3, hidx⟩ ∈ Delta l := by
  rw [mem_Delta_iff]
  have h := mem_Delta_iff.mp (P.h_in_delta (l-3) hidx)
  have hk : (P.triangles.get ⟨l-3, hidx⟩).k = l := by
    have := P.h_layers (l-3) hidx; simp only [Triple.k] at this ⊢; omega
  exact ⟨h.1, h.2.1, by linarith [h.2.2.1], hk⟩

lemma same_edge_same_triple {n : ℕ} (P Q : Pedigree n)
    (l : ℕ) (hl3 : 3 ≤ l) (hln : l ≤ n)
    (hP : l-3 < P.triangles.length) (hQ : l-3 < Q.triangles.length)
    (heq : edge_at P l = edge_at Q l) :
    P.triangles.get ⟨l-3, hP⟩ = Q.triangles.get ⟨l-3, hQ⟩ := by
  simp only [edge_at, hP, hQ, dif_pos] at heq
  obtain ⟨hi, hj⟩ := Prod.mk.inj heq
  exact Delta_ext (triple_in_Delta P l hl3 hln hP) (triple_in_Delta Q l hl3 hln hQ) hi hj

-- ============================================================================
-- DISCORDS
-- ============================================================================

def discords {n : ℕ} (P Q : Pedigree n) : Finset ℕ :=
  (Finset.Ico 4 (n + 1)).filter (fun q => edge_at P q ≠ edge_at Q q)

lemma mem_discords_iff {n : ℕ} (P Q : Pedigree n) (q : ℕ) :
    q ∈ discords P Q ↔ 4 ≤ q ∧ q ≤ n ∧ edge_at P q ≠ edge_at Q q := by
  simp [discords, Finset.mem_filter, Finset.mem_Ico]; tauto

lemma not_discord_agree {n : ℕ} (P Q : Pedigree n) (q : ℕ)
    (hq4 : 4 ≤ q) (hqn : q ≤ n) (h : q ∉ discords P Q) :
    edge_at P q = edge_at Q q := by
  simp [mem_discords_iff, hq4, hqn] at h; exact h

-- ============================================================================
-- ADJACENCY
-- ============================================================================

def AdjacentInPolytope {n : ℕ} (P Q : Pedigree n) : Prop :=
  ∀ (S : Finset (Pedigree n)) (μ : Pedigree n → ℚ),
    S.sum μ = 1 →
    (∀ R ∈ S, 0 < μ R) →
    (∀ t : Triple, t.k ≤ n →
      (char_vec P t + char_vec Q t) / 2 = S.sum (fun R => μ R * char_vec R t)) →
    S = {P, Q}

-- ============================================================================
-- LEMMA: sum = 1 forces char_vec R t = 1
-- ============================================================================

private lemma cv_eq_one_of_sum_one {n : ℕ}
    {S : Finset (Pedigree n)} {μ : Pedigree n → ℚ} {t : Triple}
    (h_sum : S.sum μ = 1) (h_pos : ∀ Z ∈ S, 0 < μ Z)
    {R : Pedigree n} (hR : R ∈ S)
    (h_eq : S.sum (fun Z => μ Z * char_vec Z t) = 1) :
    char_vec R t = 1 := by
  by_contra hne
  have h0 : char_vec R t = 0 := (char_vec_01 R t).resolve_right hne
  have hRlt : μ R * char_vec R t < μ R := by simp [h0]; exact h_pos R hR
  have hle : ∀ Z ∈ S, μ Z * char_vec Z t ≤ μ Z := fun Z hZ => by
    rcases char_vec_01 Z t with h|h <;> simp [h]; linarith [h_pos Z hZ]
  linarith [Finset.sum_lt_sum hle ⟨R, hR, hRlt⟩, h_eq ▸ h_sum]

-- ============================================================================
-- LEMMA: sum = 0 forces no positive contributor
-- ============================================================================

private lemma sum_zero_of_mid_zero {n : ℕ}
    {S : Finset (Pedigree n)} {μ : Pedigree n → ℚ} {t : Triple}
    (h_pos : ∀ Z ∈ S, 0 < μ Z)
    (h_eq : S.sum (fun Z => μ Z * char_vec Z t) = 0)
    {R : Pedigree n} (hR : R ∈ S) :
    char_vec R t = 0 := by
  by_contra hne
  have h1 : char_vec R t = 1 := (char_vec_01 R t).resolve_left hne
  have hRpos : 0 < μ R * char_vec R t := by simp [h1]; exact h_pos R hR
  have hle : ∀ Z ∈ S, 0 ≤ μ Z * char_vec Z t := fun Z hZ => by
    rcases char_vec_01 Z t with h|h <;> simp [h]; linarith [h_pos Z hZ]
  linarith [Finset.single_le_sum hle hR, h_eq ▸ hRpos]

-- ============================================================================
-- LEMMA ONEDISCARD: P and Q are adjacent if they have exactly one discord
-- ============================================================================

theorem adjacent_if_single_discord {n : ℕ} (P Q : Pedigree n)
    (h : (discords P Q).card = 1) :
    AdjacentInPolytope P Q := by
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h
  have hq_mem : q ∈ discords P Q := hq ▸ Finset.mem_singleton_self q
  have hq4  : 4 ≤ q := ((mem_discords_iff P Q q).mp hq_mem).1
  have hqn  : q ≤ n := ((mem_discords_iff P Q q).mp hq_mem).2.1
  have hq_ne : edge_at P q ≠ edge_at Q q := ((mem_discords_iff P Q q).mp hq_mem).2.2
  have h_agree : ∀ k, 4 ≤ k → k ≤ n → k ≠ q → edge_at P k = edge_at Q k := by
    intro k hk4 hkn hkq; apply not_discord_agree P Q k hk4 hkn
    intro hmem; have : k ∈ ({q} : Finset ℕ) := hq ▸ hmem
    simp at this; exact hkq this
  intro S μ h_sum h_pos h_mid
  -- Uniform length
  have hlen : ∀ X : Pedigree n, X.triangles.length = n - 2 := fun X => X.h_length
  -- Layer k index helpers
  have hidx : ∀ (X : Pedigree n) (k : ℕ), 4 ≤ k → k ≤ n → k - 3 < X.triangles.length :=
    fun X k hk4 hkn => by rw [hlen]; omega
  -- .k at position i+3 equals i+3
  have hgetk : ∀ (X : Pedigree n) (i : ℕ) (hi : i < X.triangles.length),
      (X.triangles.get ⟨i, hi⟩).k = i + 3 := by
    intro X i hi; have := X.h_layers i hi; simp only [Triple.k] at this ⊢; omega
  -- tP and tQ: P and Q's triples at the discord layer q
  have htPk : (P.triangles.get ⟨q-3, hidx P q hq4 hqn⟩).k = q := by
    have := hgetk P (q-3) (hidx P q hq4 hqn); omega
  have htQk : (Q.triangles.get ⟨q-3, hidx Q q hq4 hqn⟩).k = q := by
    have := hgetk Q (q-3) (hidx Q q hq4 hqn); omega
  -- Uniqueness: if t ∈ X.triangles and t.k = k then t = X.get ⟨k-3, _⟩
  have uniq : ∀ (X : Pedigree n) (k : ℕ) (hk4 : 4 ≤ k) (hkn : k ≤ n)
      (t : Triple) (ht : t ∈ X.triangles) (htk : t.k = k),
      t = X.triangles.get ⟨k-3, hidx X k hk4 hkn⟩ :=
    fun X k hk4 hkn t ht htk =>
      (Pedigree.unique_at_layer X k (by omega) hkn).unique
        ⟨ht, htk⟩
        ⟨List.get_mem X.triangles ⟨k-3, hidx X k hk4 hkn⟩,
         by have := hgetk X (k-3) (hidx X k hk4 hkn); omega⟩
  -- tP ≠ tQ
  have h_diff : P.triangles.get ⟨q-3, hidx P q hq4 hqn⟩ ≠
                Q.triangles.get ⟨q-3, hidx Q q hq4 hqn⟩ := by
    intro heq; apply hq_ne
    simp only [edge_at, dif_pos (hidx P q hq4 hqn), dif_pos (hidx Q q hq4 hqn)]
    exact Prod.ext (congr_arg Triple.i heq) (congr_arg Triple.j heq)
  -- tP ∉ Q.triangles, tQ ∉ P.triangles
  have hPnotQ : P.triangles.get ⟨q-3, hidx P q hq4 hqn⟩ ∉ Q.triangles := fun hc =>
    h_diff ((uniq Q q hq4 hqn _ hc htPk).trans (uniq Q q hq4 hqn _ (List.get_mem _ _) htQk).symm)
  have hQnotP : Q.triangles.get ⟨q-3, hidx Q q hq4 hqn⟩ ∉ P.triangles := fun hc =>
    h_diff.symm ((uniq P q hq4 hqn _ hc htQk).trans (uniq P q hq4 hqn _ (List.get_mem _ _) htPk).symm)
  -- Name the key triples explicitly to avoid _ synthesis failures
  let tP := P.triangles.get ⟨q-3, hidx P q hq4 hqn⟩
  let tQ := Q.triangles.get ⟨q-3, hidx Q q hq4 hqn⟩
  have hmemP : tP ∈ P.triangles := List.get_mem P.triangles ⟨q-3, hidx P q hq4 hqn⟩
  have hmemQ : tQ ∈ Q.triangles := List.get_mem Q.triangles ⟨q-3, hidx Q q hq4 hqn⟩
  have h_mid_tP : (char_vec P tP + char_vec Q tP) / 2 = 1/2 := by
    rw [char_vec_mem P tP hmemP, char_vec_not_mem Q tP hPnotQ]; norm_num
  have h_mid_tQ : (char_vec P tQ + char_vec Q tQ) / 2 = 1/2 := by
    rw [char_vec_not_mem P tQ hQnotP, char_vec_mem Q tQ hmemQ]; norm_num
  -- Core claim: any R ∈ S is P or Q
  -- Proof by contradiction: assume R ≠ P and R ≠ Q, derive contradiction.
  suffices h_either : ∀ R ∈ S, R = P ∨ R = Q by
    -- From h_either: P ∈ S and Q ∈ S
    have hP_in : P ∈ S := by
      by_contra hP_not
      -- All Z ∈ S equal Q, so char_vec Z tP = char_vec Q tP = 0
      have hall : ∀ Z ∈ S, Z = Q :=
        fun Z hZ => (h_either Z hZ).resolve_left fun heq => hP_not (heq ▸ hZ)
      have h_s := h_mid tP (by rw [htPk]; exact hqn)
      rw [h_mid_tP] at h_s
      have : S.sum (fun Z => μ Z * char_vec Z tP) = 0 :=
        Finset.sum_eq_zero fun Z hZ => by
          rw [hall Z hZ, char_vec_not_mem Q tP hPnotQ, mul_zero]
      linarith [h_s.symm ▸ this]
    have hQ_in : Q ∈ S := by
      by_contra hQ_not
      have hall : ∀ Z ∈ S, Z = P :=
        fun Z hZ => (h_either Z hZ).resolve_right fun heq => hQ_not (heq ▸ hZ)
      have h_s := h_mid tQ (by rw [htQk]; exact hqn)
      rw [h_mid_tQ] at h_s
      have : S.sum (fun Z => μ Z * char_vec Z tQ) = 0 :=
        Finset.sum_eq_zero fun Z hZ => by
          rw [hall Z hZ, char_vec_not_mem P tQ hQnotP, mul_zero]
      linarith [h_s.symm ▸ this]
    ext x; simp
    exact ⟨fun hx => (h_either x hx).imp id id,
           fun hx => hx.elim (· ▸ hP_in) (· ▸ hQ_in)⟩
  -- Prove h_either: R ∈ S → R = P ∨ R = Q
  -- Proof: assume R ≠ P and R ≠ Q, derive contradiction.
  intro R hR
  by_contra hboth
  push_neg at hboth
  obtain ⟨hRP, hRQ⟩ := hboth
  -- Step 1: R agrees with P at every non-discord layer.
  -- For each layer l ≠ q: midpoint at P's triple = 1, so R carries it.
  have h_agree_R : ∀ (l : ℕ) (hl4 : 4 ≤ l) (hln : l ≤ n) (hlq : l ≠ q),
      R.triangles.get ⟨l-3, hidx R l hl4 hln⟩ =
      P.triangles.get ⟨l-3, hidx P l hl4 hln⟩ := by
    intro l hl4 hln hlq
    -- P and Q share the same triple t0 at layer l
    have hPl := hidx P l hl4 hln
    have hQl := hidx Q l hl4 hln
    have hRl := hidx R l hl4 hln
    -- t0 = P's triple at layer l
    have ht0P : P.triangles.get ⟨l-3, hPl⟩ ∈ P.triangles := List.get_mem _ _
    have ht0Q : P.triangles.get ⟨l-3, hPl⟩ ∈ Q.triangles := by
      have heq := same_edge_same_triple P Q l (by omega) hln hPl hQl (h_agree l hl4 hln hlq)
      rw [heq]; exact List.get_mem _ _
    have ht0k : (P.triangles.get ⟨l-3, hPl⟩).k = l := by
      have := hgetk P (l-3) hPl; omega
    -- midpoint at t0 = 1
    have h_mid_t0 : (char_vec P (P.triangles.get ⟨l-3, hPl⟩) +
                     char_vec Q (P.triangles.get ⟨l-3, hPl⟩)) / 2 = 1 := by
      rw [char_vec_mem P _ ht0P, char_vec_mem Q _ ht0Q]; norm_num
    -- sum = 1 → char_vec R t0 = 1 → t0 ∈ R.triangles
    have h_sum_t0 := h_mid (P.triangles.get ⟨l-3, hPl⟩) (by rw [ht0k]; exact hln)
    rw [h_mid_t0] at h_sum_t0
    have hRt0 : P.triangles.get ⟨l-3, hPl⟩ ∈ R.triangles := by
      have := cv_eq_one_of_sum_one h_sum h_pos hR h_sum_t0.symm
      simp [char_vec] at this; exact this
    -- R's unique triple at l must be P's triple at l
    exact (uniq R l hl4 hln _ hRt0 ht0k).symm
  -- Step 2: R's triple at layer q is tR. It must equal tP or tQ.
  let tR := R.triangles.get ⟨q-3, hidx R q hq4 hqn⟩
  have htRmem : tR ∈ R.triangles := List.get_mem R.triangles ⟨q-3, hidx R q hq4 hqn⟩
  have htRk : tR.k = q := by
    simp only [tR]; have := hgetk R (q-3) (hidx R q hq4 hqn); omega
  -- If tR ∉ {tP, tQ}: midpoint at tR = 0 but R contributes μR > 0. Contradiction.
  have hcvP_tR : char_vec P tR = 0 := by
    apply char_vec_not_mem; intro hc
    exact hRP (Pedigree.ext (List.ext_get (by have := hlen P; have := hlen R; omega)
      fun i hiR hiP => by
      by_cases hiq : i = q - 3
      · subst hiq
        have h1 := uniq P q hq4 hqn tR hc htRk
        have h2 := uniq R q hq4 hqn tR htRmem htRk
        exact h2.symm.trans h1
      · by_cases hi0 : i = 0
        · subst hi0
          have hPk : (P.triangles.get ⟨0, hiP⟩).k = 3 := by have := hgetk P 0 hiP; omega
          have hRk : (R.triangles.get ⟨0, hiR⟩).k = 3 := by have := hgetk R 0 hiR; omega
          have hPd : P.triangles.get ⟨0, hiP⟩ ∈ Delta 3 := hPk ▸ P.h_in_delta 0 hiP
          have hRd : R.triangles.get ⟨0, hiR⟩ ∈ Delta 3 := hRk ▸ R.h_in_delta 0 hiR
          exact Delta_ext hRd hPd
            (by have hP := mem_Delta_iff.mp hPd
                have hR := mem_Delta_iff.mp hRd; omega)
            (by have hP := mem_Delta_iff.mp hPd
                have hR := mem_Delta_iff.mp hRd; omega)
        · have hn4 : 4 ≤ n := le_trans hq4 hqn
          have hPlen := hlen P; have hRlen := hlen R
          have hln_i : i + 3 ≤ n := by omega
          have heq := h_agree_R (i+3) (by omega) hln_i (by omega)
          simpa [show i+3-3 = i from by omega] using heq))
  have hcvQ_tR : char_vec Q tR = 0 := by
    apply char_vec_not_mem; intro hc
    exact hRQ (Pedigree.ext (List.ext_get (by have := hlen Q; have := hlen R; omega)
      fun i hiR hiQ => by
      by_cases hiq : i = q - 3
      · subst hiq
        have h1 := uniq Q q hq4 hqn tR hc htRk
        have h2 := uniq R q hq4 hqn tR htRmem htRk
        exact h2.symm.trans h1
      · by_cases hi0 : i = 0
        · subst hi0
          have hQk : (Q.triangles.get ⟨0, hiQ⟩).k = 3 := by have := hgetk Q 0 hiQ; omega
          have hRk : (R.triangles.get ⟨0, hiR⟩).k = 3 := by have := hgetk R 0 hiR; omega
          have hQd : Q.triangles.get ⟨0, hiQ⟩ ∈ Delta 3 := hQk ▸ Q.h_in_delta 0 hiQ
          have hRd : R.triangles.get ⟨0, hiR⟩ ∈ Delta 3 := hRk ▸ R.h_in_delta 0 hiR
          exact Delta_ext hRd hQd
            (by have hQ := mem_Delta_iff.mp hQd
                have hR := mem_Delta_iff.mp hRd; omega)
            (by have hQ := mem_Delta_iff.mp hQd
                have hR := mem_Delta_iff.mp hRd; omega)
        · have hn4 : 4 ≤ n := le_trans hq4 hqn
          have hQlen := hlen Q; have hRlen := hlen R
          have hln_i : i + 3 ≤ n := by omega
          have hR_l := h_agree_R (i+3) (by omega) hln_i (by omega)
          have hQP := (same_edge_same_triple P Q (i+3) (by omega) hln_i
            (hidx P (i+3) (by omega) hln_i) (hidx Q (i+3) (by omega) hln_i)
            (h_agree (i+3) (by omega) hln_i (by omega))).symm
          simpa [show i+3-3 = i from by omega] using hR_l.trans hQP.symm))
  -- Midpoint at tR = 0
  have h_mid_tR : (char_vec P tR + char_vec Q tR) / 2 = 0 := by
    rw [hcvP_tR, hcvQ_tR]; norm_num
  -- But R contributes μR > 0 to that sum
  have h_sum_tR := h_mid tR (by simp only [tR]; have := hgetk R (q-3) (hidx R q hq4 hqn); omega)
  rw [h_mid_tR] at h_sum_tR
  have hRpos : 0 < μ R * char_vec R tR := by
    rw [char_vec_mem R tR htRmem]; linarith [h_pos R hR]
  have hge : 0 < S.sum (fun Z => μ Z * char_vec Z tR) :=
    lt_of_lt_of_le hRpos (Finset.single_le_sum (f := fun Z => μ Z * char_vec Z tR)
      (fun Z hZ => by rcases char_vec_01 Z tR with h|h <;>
                      simp only [h, mul_zero, mul_one, le_refl]
                      linarith [h_pos Z hZ]) hR)
  linarith [h_sum_tR.symm ▸ hge]

end MembershipProject.Core
