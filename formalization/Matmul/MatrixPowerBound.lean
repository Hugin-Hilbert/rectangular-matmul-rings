import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# A uniform bound for rounded matrix dimensions

Rounding `q ^ k` upwards costs at most a factor of two. A tensor-leg exponent
between zero and one preserves that uniform factor.
-/

namespace Matmul.MatrixPowerBound

/-- The dimension ceiling changes the real-power estimate by at most two. -/
theorem ceil_rpow_bound {q : ℕ} (hq : 2 ≤ q) {k p t F : ℝ}
    (hk : 0 ≤ k) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ht : t + k * p ≤ F) :
    (q : ℝ) ^ t * (Nat.ceil ((q : ℝ) ^ k) : ℝ) ^ p ≤ 2 * (q : ℝ) ^ F := by
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hq0 : 0 ≤ (q : ℝ) := hq1.trans' zero_le_one
  have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hq1
  have hk1 : 1 ≤ (q : ℝ) ^ k := Real.one_le_rpow hq1 hk
  have hceil : (Nat.ceil ((q : ℝ) ^ k) : ℝ) ≤ 2 * (q : ℝ) ^ k := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hq0 k)
    linarith
  have hceilp := Real.rpow_le_rpow (Nat.cast_nonneg _) hceil hp
  have h2p : (2 : ℝ) ^ p ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ)) hp1
  calc
    (q : ℝ) ^ t * (Nat.ceil ((q : ℝ) ^ k) : ℝ) ^ p ≤
        (q : ℝ) ^ t * (2 * (q : ℝ) ^ k) ^ p :=
      mul_le_mul_of_nonneg_left hceilp (Real.rpow_nonneg hq0 t)
    _ = (2 : ℝ) ^ p * (q : ℝ) ^ (t + k * p) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hq0 k),
        ← Real.rpow_mul hq0 k p, Real.rpow_add hqpos]
      ring
    _ ≤ 2 * (q : ℝ) ^ (t + k * p) :=
      mul_le_mul_of_nonneg_right h2p (Real.rpow_nonneg hq0 _)
    _ ≤ 2 * (q : ℝ) ^ F :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 ht)
        (by norm_num)

end Matmul.MatrixPowerBound
