-- Core\Basic.lean
import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
set_option linter.unusedVariables false
open Nat
-- Copyied from PedigreeMain.lean: lines for BASIC DEFINITIONS section
namespace MembershipProject.Core
structure Edge (k : Nat) where
  i : Nat
  j : Nat
  hi : i < k
  hj : j < k
  hij : i < j
deriving DecidableEq, Repr

structure GenVar (k : Nat) where
  i : Nat
  j : Nat
  hi : i < k
  hj : j < k
  hij : i < j
deriving DecidableEq, Repr

def GenVector (k : Nat) := GenVar k → Rat
def SlackVector (k : Nat) := Edge k → Rat

structure SparseGenerationMatrix (k : Nat) where
  hk : k ≥ 3
end MembershipProject.Core
