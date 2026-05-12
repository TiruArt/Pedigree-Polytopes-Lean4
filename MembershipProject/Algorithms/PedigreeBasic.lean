-- PedigreeBasic.lean
-- Standalone implementation without mathlib

structure Node where
  i : Nat
  j : Nat
  k : Nat

def Node.toString (n : Node) : String :=
  s!"({n.i},{n.j},{n.k})"

instance : ToString Node where
  toString := Node.toString

def nodes_in_layer (k : Nat) : List Node :=
  if k < 3 then []
  else
    let rec loop_i (i : Nat) : List Node :=
      if i ≥ k - 1 then []
      else
        let rec loop_j (j : Nat) : List Node :=
          if j ≥ k - 1 then []
          else
            if i < j ∧ j < k - 1 then
              { i := i + 1, j := j + 1, k := k } :: loop_j (j + 1)
            else
              loop_j (j + 1)
        loop_j (i + 1) ++ loop_i (i + 1)
    loop_i 0

#eval nodes_in_layer 4
