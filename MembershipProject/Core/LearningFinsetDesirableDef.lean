import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open Finset

/- --- 1. PREDICATES (Prop) --- -/

def isPreSolution (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  S.card = n - 2 ∧
  (∀ t ∈ S, t.card = 3) ∧
  (∀ k ∈ Icc 3 n, ∃! t ∈ S, t.max = some k)

def isSolution (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  isPreSolution n S ∧
  ∀ t1 ∈ S, ∀ t2 ∈ S,
    let k1 := t1.max.getD 0
    let k2 := t2.max.getD 0
    (k1 ≥ 4 ∧ k2 ≥ 4 ∧ k1 < k2) → (t1.erase k1) ≠ (t2.erase k2)

/-- A Pedigree on n vertices is a Finset of 3-element Finsets satisfying
    the layered structure, generator, and distinctness conditions. -/
def Pedigree (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  isSolution n S ∧ ∀ t ∈ S,
    let k := t.max.getD 0
    let pair := t.erase k
    let a := pair.min.getD 0
    let b := pair.max.getD 0
    (pair ⊆ {1, 2, 3}) ∨ (∃ t_prev ∈ S, t_prev.max = some b ∧ a ∈ t_prev)

/- --- 2. COMPUTABLE CHECKERS (Bool) --- -/

def checkPreSolution (n : ℕ) (S : Finset (Finset ℕ)) : Bool :=
  (S.card == n - 2) &&
  (S.filter (λ t => t.card != 3)).card == 0 &&
  ((Icc 3 n).filter (λ k => (S.filter (λ t => t.max == some k)).card != 1)).card == 0

def checkSolution (n : ℕ) (S : Finset (Finset ℕ)) : Bool :=
  checkPreSolution n S &&
  let trips := S.filter (λ t => t.max.getD 0 ≥ 4)
  (trips.filter (λ t1 =>
    (trips.filter (λ t2 =>
      let k1 := t1.max.getD 0
      let k2 := t2.max.getD 0
      k1 < k2 && (t1.erase k1) == (t2.erase k2)
    )).card != 0
  )).card == 0

/-- Computable checker for Pedigree -/
def checkPedigree (n : ℕ) (S : Finset (Finset ℕ)) : Bool :=
  checkSolution n S &&
  (S.filter (λ t =>
    let k := t.max.getD 0
    let pair := t.erase k
    let a := pair.min.getD 0
    let b := pair.max.getD 0
    let primitive := pair ⊆ {1, 2, 3}
    let justified := (S.filter (λ tp => tp.max == some b && a ∈ tp)).card != 0
    !(primitive || justified)
  )).card == 0

/- --- 3. EXAMPLES AND VERIFICATION --- -/

def S5_natural : Finset (Finset ℕ) := {{1, 2, 3}, {2, 3, 4}, {3, 4, 5}}
def S5_prime   : Finset (Finset ℕ) := {{1, 2, 3}, {1, 3, 4}, {3, 4, 5}}
def S5_fail    : Finset (Finset ℕ) := {{1, 2, 3}, {1, 2, 4}, {3, 4, 5}}

#eval checkPedigree 5 S5_natural -- true
#eval checkPedigree 5 S5_prime   -- true
#eval checkPedigree 5 S5_fail    -- false

def S6_natural : Finset (Finset ℕ) := {{1, 2, 3}, {2, 3, 4}, {3, 4, 5}, {4, 5, 6}}
#eval checkPedigree 6 S6_natural -- true
