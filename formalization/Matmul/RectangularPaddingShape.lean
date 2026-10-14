import Matmul.RecursiveCost
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Rectangular dimensions at a common padding depth

If a recursion uses an outer base `a` and a rectangular base `b` with
`a^k ≤ b`, every input of width `ceil (n^k)` fits into the corresponding
width `b^t` whenever its outer dimension fits into `a^t`.
-/

namespace Matmul.RectangularPaddingShape

/-- A rectangular input dimension fits at every depth where the outer
dimension fits. The ceiling is a natural-number ceiling. -/
theorem ceil_rpow_le_pow_of_le_pow (a b n t : ℕ) (k : ℝ)
    (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ)) (hn : n ≤ a ^ t) :
    Nat.ceil ((n : ℝ) ^ k) ≤ b ^ t := by
  apply Nat.ceil_le.mpr
  have hnR : (n : ℝ) ≤ (a : ℝ) ^ t := by exact_mod_cast hn
  calc
    (n : ℝ) ^ k ≤ ((a : ℝ) ^ t) ^ k :=
      Real.rpow_le_rpow (by positivity) hnR hk
    _ = ((a : ℝ) ^ k) ^ t :=
      (Real.rpow_pow_comm (by positivity : 0 ≤ (a : ℝ)) k t).symm
    _ ≤ (b : ℝ) ^ t :=
      pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) k) hab t
    _ = (b ^ t : ℕ) := by norm_cast

/-- Padding the outer dimension to its next base power also pads its
rectangular `ceil (n^k)` dimension at the same logarithmic depth. -/
theorem ceil_rpow_le_padding_pow (a b n : ℕ) (k : ℝ)
    (ha : 1 < a) (hn : 0 < n) (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ)) :
    Nat.ceil ((n : ℝ) ^ k) ≤ b ^ (Nat.log a n + 1) := by
  exact ceil_rpow_le_pow_of_le_pow a b n (Nat.log a n + 1) k hk hab
    (Matmul.RecursiveCost.padding_size_bounds a n ha hn).1

#print axioms ceil_rpow_le_pow_of_le_pow
#print axioms ceil_rpow_le_padding_pow

end Matmul.RectangularPaddingShape
