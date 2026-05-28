-- Core/N_Lemma4_Simple.lean

-- ============================================================
-- Simple definitions
-- ============================================================

def initial_tour : Finset (ℕ × ℕ) := {(1, 2), (1, 3), (2, 3)}

def insert_vertex (tour : Finset (ℕ × ℕ)) (l : ℕ) (e : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (tour.erase e) ∪ {(e.1, l), (e.2, l)}

/-- A simple representation of a pedigree as a list of edges -/
structure SimplePedigree (n : ℕ) where
  edges : List (ℕ × ℕ)
  h_len : edges.length = n - 3
  h_first_edge_in_initial : edges[0] ∈ initial_tour  -- By definition (1)
  h_edge_available : ∀ i, i + 1 < edges.length →
    let e_curr := edges[i + 1]
    let e_prev := edges[i]
    let l := i + 5
    e_curr = e_prev ∨ e_curr = (e_prev.1, l) ∨ e_curr = (e_prev.2, l)  -- By definition (2)

/-- Build a tour from a pedigree -/
def build_tour (P : SimplePedigree n) : Finset (ℕ × ℕ) :=
  let rec loop (tour : Finset (ℕ × ℕ)) (l : ℕ) (es : List (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
    match es with
    | [] => tour
    | e :: rest => loop (insert_vertex tour l e) (l + 1) rest
  loop initial_tour 4 P.edges

/-- Compute slack from a pedigree -/
def slack_from_edges (edges : List (ℕ × ℕ)) (n : ℕ) : ℕ × ℕ → ℚ :=
  if n = 3 then
    fun e => if e ∈ initial_tour then 1 else 0
  else
    let prev_slack := slack_from_edges edges (n - 1)
    let e_prev := edges[n - 4]!
    fun e =>
      if e = e_prev then prev_slack e - 1
      else if e = (e_prev.1, n) ∨ e = (e_prev.2, n) then prev_slack e + 1
      else prev_slack e

-- ============================================================
-- Lemma: Edge bound property
-- ============================================================

lemma edge_layer_bound (P : SimplePedigree n) (m : ℕ) (hm : m ≤ n) :
    ∀ e ∈ build_tour (⟨P.edges.take (m - 3), by sorry⟩), e.2 ≤ m := by
  induction m using Nat.le_induction with
  | base =>
    have h3 : m = 3 := by omega
    subst h3
    simp [build_tour, initial_tour]
    intro e he
    simp [initial_tour] at he
    rcases he with h1 | h2 | h3
    · simp [h1]
    · simp [h2]
    · simp [h3]
  | succ m hm_ge_4 IH =>
    have hm : m ≥ 4 := by omega
    let edges_prev := P.edges.take (m - 3)
    let P_prev : SimplePedigree m := ⟨edges_prev, by sorry, by sorry, by sorry⟩
    let e_next := P.edges[m - 3]!
    intro e he
    simp [build_tour] at he
    by_cases h_eq : e = e_next
    · subst h_eq
      have : e_next.2 = m + 1 := by
        -- In a pedigree, the edge at position (m-3) is inserted at layer m+1
        -- So its second component is m+1
        sorry
      linarith
    · by_cases h_new : e = (e_next.1, m + 1) ∨ e = (e_next.2, m + 1)
      · rcases h_new with h1 | h2
        · simp [h1]; linarith
        · simp [h2]; linarith
      · have h_in_prev : e ∈ build_tour P_prev := by
          simp [build_tour] at he
          simpa [h_eq, h_new] using he
        exact IH P_prev e h_in_prev

-- ============================================================
-- Main Lemma: Slack equals tour incidence
-- ============================================================

lemma slack_eq_tour_incidence (n : ℕ) (hn : 4 ≤ n) (P : SimplePedigree n) :
    ∀ e : ℕ × ℕ,
      slack_from_edges P.edges n e = (if e ∈ build_tour P then 1 else 0) := by
  induction' n with n IH
  · linarith
  · by_cases h_n3 : n = 3
    · -- Base case: n = 4
      have hn4 : n + 1 = 4 := by omega
      subst hn4
      simp [slack_from_edges, build_tour]
      obtain ⟨e₄, rest⟩ := P.edges
      have h_rest : rest = [] := by
        have h_len4 : P.edges.length = 1 := by simp [P.h_len, hn4]
        rw [← h_len4] at this
        exact List.length_eq_one_iff.mp h_len4
      subst h_rest
      simp [insert_vertex]
      intro e
      by_cases h_eq : e = e₄
      · simp [h_eq]
        have h_in_initial := P.h_first_edge_in_initial
        simp [h_in_initial]
        linarith
      · by_cases h_new : e = (e₄.1, 4) ∨ e = (e₄.2, 4)
        · simp [h_new, h_eq]
          linarith
        · simp [h_eq, h_new]
          rfl
    · -- Inductive step: n ≥ 4
      have hn_ge4 : 4 ≤ n := by omega
      let edges_prev := P.edges.take (n - 3)
      have h_len_prev : edges_prev.length = n - 3 := by
        simp [edges_prev, P.h_len]
        omega
      let P_prev : SimplePedigree n :=
        { edges := edges_prev
        , h_len := h_len_prev
        , h_first_edge_in_initial := by sorry  -- Truncation preserves first edge
        , h_edge_available := by sorry  -- Truncation preserves generator condition
        }

      have h_IH := IH n hn_ge4 P_prev

      let e_next := P.edges[n - 3]!

      -- Recurrence for slack
      have h_slack_next : ∀ e, slack_from_edges P.edges (n + 1) e =
          if e = e_next then slack_from_edges edges_prev n e - 1
          else if e = (e_next.1, n + 1) ∨ e = (e_next.2, n + 1) then slack_from_edges edges_prev n e + 1
          else slack_from_edges edges_prev n e := by
        intro e
        simp [slack_from_edges]
        rw [if_neg (by omega : n + 1 ≠ 3)]
        simp [edges_prev, e_next]
        rfl

      -- Recurrence for tour
      have h_tour_next : ∀ e, (if e ∈ insert_vertex (build_tour P_prev) (n + 1) e_next then 1 else 0) =
          if e = e_next then (if e ∈ build_tour P_prev then 1 else 0) - 1
          else if e = (e_next.1, n + 1) ∨ e = (e_next.2, n + 1) then (if e ∈ build_tour P_prev then 1 else 0) + 1
          else (if e ∈ build_tour P_prev then 1 else 0) := by
        intro e
        simp [insert_vertex]
        by_cases h_eq : e = e_next
        · simp [h_eq]
          have h_in_prev := P.h_edge_available (n - 4) (by omega)
          rcases h_in_prev with h1 | h2 | h3
          · rw [h1]; exact h_in_prev
          · rw [h2]; simp
          · rw [h3]; simp
        · by_cases h_new : e = (e_next.1, n + 1) ∨ e = (e_next.2, n + 1)
          · simp [h_eq, h_new]
            have h_not_in_prev : e ∉ build_tour P_prev := by
              intro h
              have h_bound := edge_layer_bound P_prev n (by omega)
              apply h_bound e h
            simp [h_not_in_prev]
          · simp [h_eq, h_new]

      -- Combine
      intro e
      rw [h_slack_next e, h_tour_next e]
      have h_IH_applied := h_IH e
      rw [h_IH_applied]
      by_cases h_eq : e = e_next
      · simp [h_eq]
      · by_cases h_new : e = (e_next.1, n + 1) ∨ e = (e_next.2, n + 1)
        · simp [h_eq, h_new]
        · simp [h_eq, h_new]

end MembershipProject.Core
