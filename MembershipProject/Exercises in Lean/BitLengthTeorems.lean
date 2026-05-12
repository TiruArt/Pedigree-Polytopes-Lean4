import Mathlib.Tactic
import Mathlib.Data.Rat.Defs
--import Mathlib.Data.Rat.Basic
def bitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

#eval bitLength 0      -- 0
#eval bitLength 1      -- 1
#eval bitLength 2      -- 2
#eval bitLength 3      -- 2
#eval bitLength 4      -- 3
#eval bitLength 7      -- 3
#eval bitLength 8      -- 4
#eval bitLength 15     -- 4  (binary: 1111)
#eval bitLength 16     -- 5  (binary: 10000)
-- Some btheorems about bitLength of powers of two


-- Theorem 1: Exact value
theorem bitLength_pow_two (k : Nat) : bitLength (2^k) = k + 1 := by
  by_cases h : 2^k = 0
  · exfalso
    exact pow_ne_zero k (by decide) h
  · simp [bitLength,  Nat.log2_two_pow]

-- Theorem 2: Bounds
theorem bitLength_pos (n : Nat) (h : 0 < n) : 0 < bitLength n := by
  simp [bitLength, (Nat.pos_iff_ne_zero.mp h)]

theorem bitLength_le (n : Nat) : bitLength n ≤ n + 1 := by
  by_cases h : n = 0
  · simp [bitLength, h]
  · simp [bitLength, h]
    have : Nat.log2 n ≤ n := Nat.log2_le_self n
    omega



def ratBitLengthUpper (q : ℚ) : ℕ :=
  1 + bitLength q.num.natAbs + bitLength q.den

-- First, some basic properties
theorem ratBitLengthUpper_nonneg (q : ℚ) : 0 ≤ ratBitLengthUpper q := by
  unfold ratBitLengthUpper
  omega

theorem ratBitLengthUpper_zero : ratBitLengthUpper (0 : ℚ) = 2 := by
  simp [ratBitLengthUpper, bitLength]; decide

theorem ratBitLengthUpper_one : ratBitLengthUpper (1 : ℚ) = 3 := by
  simp [ratBitLengthUpper, bitLength]
  decide

theorem ratBitLengthUpper_neg (q : ℚ) : ratBitLengthUpper (-q) = ratBitLengthUpper q := by
  simp [ratBitLengthUpper]

-- Now for operations: Addition

-- For addition, the result's numerator and denominator can grow
-- A simple (but loose) bound: sum of bit lengths


-- Let's prove a polynomial bound:
import Mathlib.Tactic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Defs

-- Bit length for natural numbers
def bitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

-- Upper bound for rational bit length: 1 (sign) + bits for |num| + bits for den
def ratBitLengthUpper (q : ℚ) : ℕ :=
  1 + bitLength q.num.natAbs + bitLength q.den

-- Helper theorem: bitLength is monotonic
theorem bitLength_monotone (m n : Nat) (h : m ≤ n) : bitLength m ≤ bitLength n := by
  by_cases hm : m = 0
  · simp [bitLength, hm]
  · by_cases hn : n = 0
    · rw [hn] at h
      have : m = 0 := by omega
      contradiction
    · simp [bitLength, hm, hn]
      exact Nat.log2_mono h

-- Helper theorem: bitLength of product ≤ sum of bitLengths
theorem bitLength_mul_le (x y : ℕ) : bitLength (x * y) ≤ bitLength x + bitLength y := by
  by_cases hx : x = 0
  · simp [hx, bitLength]
  · by_cases hy : y = 0
    · simp [hy, bitLength]
    · exact Nat.log2_mul_le x y

-- Helper theorem: bitLength(n+1) ≤ bitLength(n) + 1
theorem bitLength_succ_le (n : ℕ) : bitLength (n + 1) ≤ bitLength n + 1 :=
  Nat.log2_succ_le n

-- Basic properties
theorem ratBitLengthUpper_nonneg (q : ℚ) : 0 ≤ ratBitLengthUpper q := by
  unfold ratBitLengthUpper
  omega

theorem ratBitLengthUpper_zero : ratBitLengthUpper (0 : ℚ) = 2 := by
  simp [ratBitLengthUpper, bitLength]

theorem ratBitLengthUpper_one : ratBitLengthUpper (1 : ℚ) = 3 := by
  simp [ratBitLengthUpper, bitLength]

-- Negation doesn't change bit length
theorem ratBitLengthUpper_neg (q : ℚ) : ratBitLengthUpper (-q) = ratBitLengthUpper q := by
  simp [ratBitLengthUpper]

-- Reciprocal has exactly the same bit length (for nonzero)
theorem ratBitLengthUpper_inv (q : ℚ) (hq : q ≠ 0) :
    ratBitLengthUpper (q⁻¹) = ratBitLengthUpper q := by
  unfold ratBitLengthUpper
  simp [Rat.inv_def, hq]

-- Multiplication bound: output ≤ 2*(sum of inputs)
theorem ratBitLengthUpper_mul_bound (q r : ℚ) :
    ratBitLengthUpper (q * r) ≤ 2 * (ratBitLengthUpper q + ratBitLengthUpper r) := by
  unfold ratBitLengthUpper
  let A := bitLength q.num.natAbs
  let B := bitLength q.den
  let C := bitLength r.num.natAbs
  let D := bitLength r.den

  -- Conservative bounds: result ≤ product of inputs
  have hB_pos : 0 < q.den := Rat.den_pos q
  have hD_pos : 0 < r.den := Rat.den_pos r

  -- For multiplication: (a/b) * (c/d) reduces (a*c)/(b*d)
  have num_le : (q * r).num.natAbs ≤ q.num.natAbs * r.num.natAbs := by
    have : (q * r).num ∣ q.num * r.num := by
      rw [Rat.mul_num]
    exact Int.natAbs_le_natAbs_of_dvd this

  have den_le : (q * r).den ≤ q.den * r.den := by
    have : (q * r).den ∣ q.den * r.den := by
      rw [Rat.mul_den]
    exact Nat.le_of_dvd (mul_pos hB_pos hD_pos) this

  -- Apply bitLength bounds
  have h1 : bitLength ((q * r).num.natAbs) ≤ bitLength (q.num.natAbs * r.num.natAbs) :=
    bitLength_monotone _ _ num_le
  have h2 : bitLength (q.num.natAbs * r.num.natAbs) ≤ A + C :=
    bitLength_mul_le _ _

  have h3 : bitLength ((q * r).den) ≤ bitLength (q.den * r.den) :=
    bitLength_monotone _ _ den_le
  have h4 : bitLength (q.den * r.den) ≤ B + D :=
    bitLength_mul_le _ _

  -- Denominators have bitLength ≥ 1
  have hB : 1 ≤ B := by
    simp [bitLength, hB_pos.ne.symm]
  have hD : 1 ≤ D := by
    simp [bitLength, hD_pos.ne.symm]

  omega

-- Division bound: q / r = q * (r⁻¹)
theorem ratBitLengthUpper_div_bound (q r : ℚ) (hr : r ≠ 0) :
    ratBitLengthUpper (q / r) ≤ 2 * (ratBitLengthUpper q + ratBitLengthUpper r) :=
  calc
    ratBitLengthUpper (q / r) = ratBitLengthUpper (q * r⁻¹) := rfl
    _ ≤ 2 * (ratBitLengthUpper q + ratBitLengthUpper (r⁻¹)) :=
      ratBitLengthUpper_mul_bound q (r⁻¹)
    _ = 2 * (ratBitLengthUpper q + ratBitLengthUpper r) := by
      simp [ratBitLengthUpper_inv r hr]

-- Addition bound: output ≤ 4 * max(inputs)
theorem ratBitLengthUpper_add_bound (q r : ℚ) :
    ratBitLengthUpper (q + r) ≤ 4 * max (ratBitLengthUpper q) (ratBitLengthUpper r) := by
  unfold ratBitLengthUpper
  let A := bitLength q.num.natAbs
  let B := bitLength q.den
  let C := bitLength r.num.natAbs
  let D := bitLength r.den

  have hB_pos : 0 < q.den := Rat.den_pos q
  have hD_pos : 0 < r.den := Rat.den_pos r

  -- Very conservative bound for addition: (a/b) + (c/d) = (a*d + c*b)/(b*d)
  -- Numerator ≤ (|a|+1)*(|c|+1)*(b+1)*(d+1) (definitely true)
  have num_bound : (q + r).num.natAbs ≤ (q.num.natAbs + 1) * (r.num.natAbs + 1) * (q.den + 1) * (r.den + 1) := by
    omega

  -- Denominator after reduction divides b*d
  have den_bound : (q + r).den ≤ q.den * r.den := by
    have : (q + r).den ∣ q.den * r.den := by
      exact Rat.add_den_dvd q r
    exact Nat.le_of_dvd (mul_pos hB_pos hD_pos) this

  -- Bit length bounds
  have h_den : bitLength ((q + r).den) ≤ B + D := by
    calc
      bitLength ((q + r).den) ≤ bitLength (q.den * r.den) := bitLength_monotone _ _ den_bound
      _ ≤ B + D := bitLength_mul_le _ _

  -- Conservative bound for numerator
  have h_num : bitLength ((q + r).num.natAbs) ≤ A + C + B + D + 4 := by
    calc
      bitLength ((q + r).num.natAbs) ≤
          bitLength ((q.num.natAbs + 1) * (r.num.natAbs + 1) * (q.den + 1) * (r.den + 1)) :=
        bitLength_monotone _ _ num_bound
      _ ≤ bitLength ((q.num.natAbs + 1) * (r.num.natAbs + 1) * (q.den + 1)) + bitLength (r.den + 1) :=
        bitLength_mul_le _ _
      _ ≤ (bitLength ((q.num.natAbs + 1) * (r.num.natAbs + 1)) + bitLength (q.den + 1)) +
           bitLength (r.den + 1) := by
        gcongr
        exact bitLength_mul_le _ _
      _ ≤ ((bitLength (q.num.natAbs + 1) + bitLength (r.num.natAbs + 1)) + bitLength (q.den + 1)) +
           bitLength (r.den + 1) := by
        gcongr
        exact bitLength_mul_le _ _
      _ ≤ ((A + 1) + (C + 1)) + (B + 1) + (D + 1) := by
        repeat' gcongr
        · exact bitLength_succ_le (q.num.natAbs)
        · exact bitLength_succ_le (r.num.natAbs)
        · exact bitLength_succ_le (q.den)
        · exact bitLength_succ_le (r.den)
      _ = A + C + B + D + 4 := by ring

  -- Denominator bit lengths ≥ 1
  have hB : 1 ≤ B := by
    simp [bitLength, hB_pos.ne.symm]
  have hD : 1 ≤ D := by
    simp [bitLength, hD_pos.ne.symm]

  let M := max (1 + A + B) (1 + C + D)
  have hA : A ≤ M := by omega
  have hB' : B ≤ M := by omega
  have hC : C ≤ M := by omega
  have hD' : D ≤ M := by omega

  calc
    1 + bitLength ((q + r).num.natAbs) + bitLength ((q + r).den)
        ≤ 1 + (A + C + B + D + 4) + (B + D) := by omega
    _ = 5 + A + 2*B + C + 2*D := by ring
    _ ≤ 4 * M := by
      omega
    _ = 4 * max (ratBitLengthUpper q) (ratBitLengthUpper r) := by
      simp [ratBitLengthUpper, M]

-- Subtraction: q - r = q + (-r)
theorem ratBitLengthUpper_sub_bound (q r : ℚ) :
    ratBitLengthUpper (q - r) ≤ 4 * max (ratBitLengthUpper q) (ratBitLengthUpper r) := by
  calc
    ratBitLengthUpper (q - r) = ratBitLengthUpper (q + (-r)) := by ring
    _ ≤ 4 * max (ratBitLengthUpper q) (ratBitLengthUpper (-r)) :=
      ratBitLengthUpper_add_bound q (-r)
    _ = 4 * max (ratBitLengthUpper q) (ratBitLengthUpper r) := by
      simp

-- Test cases
#eval ratBitLengthUpper (0 : ℚ)      -- 2
#eval ratBitLengthUpper (1 : ℚ)      -- 3
#eval ratBitLengthUpper (-1 : ℚ)     -- 3
#eval ratBitLengthUpper (1/2 : ℚ)    -- 1 + 1 + 2 = 4
#eval ratBitLengthUpper (-3/4 : ℚ)   -- 1 + 2 + 3 = 6
#eval ratBitLengthUpper (7/1 : ℚ)    -- 1 + 3 + 1 = 5
