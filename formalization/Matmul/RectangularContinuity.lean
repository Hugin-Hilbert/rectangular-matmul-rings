import Matmul.RectangularOptimization
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
# Rational upper approximation of the rectangular curve

The optimization formulation gives a direct one-sided Lipschitz bound.
Thus irrational aspect ratios can be padded to rational aspect ratios
without a separate differentiation or continuity proof of the formula.
-/

namespace Matmul.RectangularOptimization

theorem feasible_second_le_one {a b : ℝ} (hab : Feasible a b) : b ≤ 1 := by
  have hs := sq_nonneg (2 * a - 1)
  have hb := hab.2.2.2
  nlinarith

theorem rectangularBound_mono {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l)
    (hkl : k ≤ l) : rectangularBound k ≤ rectangularBound l := by
  obtain ⟨a, b, hab, hvalue⟩ := bound_attained hk
  have hobj := objective_le_of_feasible hab hl
  have hinc := mul_nonneg (sub_nonneg.mpr hkl) hab.2.2.1
  rw [← hvalue]
  nlinarith

theorem rectangularBound_le_add_delta {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l)
    (hkl : k ≤ l) : rectangularBound l ≤ rectangularBound k + (l - k) := by
  obtain ⟨a, b, hab, hvalue⟩ := bound_attained hl
  have hobj := objective_le_of_feasible hab hk
  have hinc := mul_le_mul_of_nonneg_left (feasible_second_le_one hab)
    (sub_nonneg.mpr hkl)
  rw [← hvalue]
  nlinarith

theorem two_le_rectangularBound {k : ℝ} (hk : 0 ≤ k) : 2 ≤ rectangularBound k := by
  have h := objective_le_of_feasible (a := 1) (b := 0)
    (by norm_num [Feasible]) hk
  simpa using h

theorem exists_rational_upper_close {k ε : ℝ} (hk : 0 ≤ k) (hε : 0 < ε) :
    ∃ q : ℚ, k < (q : ℝ) ∧ 0 ≤ (q : ℝ) ∧
      rectangularBound (q : ℝ) < rectangularBound k + ε := by
  obtain ⟨q, hqk, hql⟩ := exists_rat_btwn (lt_add_of_pos_right k hε)
  have hq : 0 ≤ (q : ℝ) := hk.trans hqk.le
  have h := rectangularBound_le_add_delta hk hq hqk.le
  exact ⟨q, hqk, hq, by linarith⟩

#print axioms rectangularBound_le_add_delta
#print axioms exists_rational_upper_close

end Matmul.RectangularOptimization
