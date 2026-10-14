import Mathlib

namespace Matmul.Homogeneous

/-- An affine upper bound and a secant lower bound give a row increment. -/
theorem row_increment_of_affine_bound {q : ℝ → ℝ} {L c s h : ℝ}
    (hs : 0 < s) (hh : 0 < h) (hc : 0 ≤ c)
    (hcap : q s ≤ L * (s + c))
    (hinc : L * h ≤ q (s + h) - q s) :
    q s * (1 + h / (s + c)) ≤ q (s + h) := by
  have hden : 0 < s + c := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcap hh.le
  have hterm : q s * (h / (s + c)) ≤ L * h := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  nlinarith

/-- Raising a positive powered comparison restores the original row. -/
theorem row_power_increment {x y a z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (ha : 0 < a) (hz : 0 ≤ z)
    (h : x ^ (1 / a) * z ≤ y ^ (1 / a)) : x * z ^ a ≤ y := by
  have hp := Real.rpow_le_rpow
    (mul_nonneg (Real.rpow_nonneg hx.le _) hz) h ha.le
  rw [Real.mul_rpow (Real.rpow_nonneg hx.le _) hz] at hp
  simpa only [one_div, Real.rpow_inv_rpow hx.le ha.ne',
    Real.rpow_inv_rpow hy.le ha.ne'] using hp

/-- Homogeneous row scaling transports the normalized secant increment. -/
theorem increment_of_row_affine_bound {U : ℝ → ℝ → ℝ} {a L c : ℝ}
    (hpos : ∀ r s, 0 < r → 0 < s → 0 < U r s)
    (hhom : ∀ r s, 0 < r → 0 < s → U r s = r * U 1 (s / r))
    (ha : 0 < a) (_hL : 0 < L) (hc : 0 ≤ c)
    (hcap : ∀ s, 0 < s → U 1 s ^ (1 / a) ≤ L * (s + c))
    (hinc : ∀ x y, 0 < x → x < y →
      L * (y - x) ≤ U 1 y ^ (1 / a) - U 1 x ^ (1 / a))
    (r s h : ℝ) (hr : 0 < r) (hs : 0 < s) (hh : 0 < h) :
    U r s * (1 + h / (s + c * r)) ^ a ≤ U r (s + h) := by
  have hsr : 0 < s / r := div_pos hs hr
  have hhr : 0 < h / r := div_pos hh hr
  have hsadd : 0 < s / r + h / r := by positivity
  have hsec := hinc (s / r) (s / r + h / r) hsr (by linarith)
  simp only [add_sub_cancel_left] at hsec
  have hrow := row_increment_of_affine_bound
    (q := fun t => U 1 t ^ (1 / a)) hsr hhr hc (hcap _ hsr) hsec
  have hbase : 0 ≤ 1 + (h / r) / (s / r + c) := by positivity
  have hpow := row_power_increment
    (hpos 1 (s / r) (by norm_num) hsr)
    (hpos 1 (s / r + h / r) (by norm_num) hsadd) ha hbase hrow
  have hden : 0 < s + c * r := by positivity
  have hfactor : 1 + (h / r) / (s / r + c) = 1 + h / (s + c * r) := by
    field_simp [hr.ne', hden.ne']
  rw [hfactor] at hpow
  rw [← add_div] at hpow
  have hscaled := mul_le_mul_of_nonneg_left hpow hr.le
  rw [hhom r s hr hs, hhom r (s + h) hr (by positivity)]
  nlinarith

#print axioms increment_of_row_affine_bound

end Matmul.Homogeneous
