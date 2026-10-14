import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A discrete logarithmic potential with a summable quadratic error. -/

namespace Matmul.DiscretePotential

/-- An elementary lower bound, derived from the standard rational log bound. -/
theorem log_one_add_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg hx)
  apply (le_div_iff₀ (by positivity : 0 < x + 2)).2
  nlinarith [mul_nonneg hx (sq_nonneg x)]

theorem log_nat_step_error {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ 1 / (n : ℝ) - (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) ∧
      1 / (n : ℝ) - (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) ≤
        1 / (n : ℝ) ^ 2 := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have heq : Real.log ((n + 1 : ℕ) : ℝ) - Real.log n =
      Real.log (1 + 1 / (n : ℝ)) := by
    rw [← Real.log_div (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0) (ne_of_gt hnpos)]
    congr 1
    push_cast
    field_simp
  rw [heq]
  have hu := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / (n : ℝ))
  have hl := log_one_add_lower (by positivity : 0 ≤ 1 / (n : ℝ))
  have hsq : (1 / (n : ℝ)) ^ 2 = 1 / (n : ℝ) ^ 2 := by ring
  rw [hsq] at hl
  constructor <;> nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    (sq_nonneg (n : ℝ))]

/-- The quadratic error has a finite telescoping majorant. -/
theorem inv_sq_le_telescope {n : ℕ} (hn : 2 ≤ n) :
    1 / (n : ℝ) ^ 2 ≤ 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have heq : 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) =
      1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    field_simp
    ring
  rw [heq]
  apply one_div_le_one_div_of_le
  · exact mul_pos (by linarith) (by linarith)
  · nlinarith

/-- A pointwise `1/n²` error cannot change the logarithmic growth coefficient.
The coefficients may be arbitrary real numbers. -/
theorem growth_coefficient_le (W : ℕ → ℝ) (A B H C : ℝ)
    (hstep : ∀ n : ℕ, 2 ≤ n →
      A / (n : ℝ) - B / (n : ℝ) ^ 2 ≤ W (n + 1) - W n)
    (hupper : ∀ n : ℕ, 2 ≤ n → W n ≤ H * Real.log n + C) : A ≤ H := by
  let K : ℝ := |A| + |B|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hstep' (n : ℕ) (hn : 2 ≤ n) :
      A * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) - K / (n : ℝ) ^ 2 ≤
        W (n + 1) - W n := by
    have he := log_nat_step_error hn
    have hden : 0 ≤ 1 / (n : ℝ) ^ 2 := by positivity
    have hA := neg_abs_le A
    have hB := le_abs_self B
    have hmul1 := mul_le_mul_of_nonneg_right hA he.1
    have hmul2 := mul_le_mul_of_nonneg_left he.2 (abs_nonneg A)
    have hmul3 := mul_le_mul_of_nonneg_right hB hden
    have hs := hstep n hn
    dsimp [K]
    simp only [div_eq_mul_inv, one_mul] at *
    nlinarith
  have hlower (n : ℕ) (hn : 2 ≤ n) :
      W 2 + A * (Real.log n - Real.log 2) - K + K / ((n : ℝ) - 1) ≤ W n := by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      have hs := hstep' n hn
      have ht := mul_le_mul_of_nonneg_left (inv_sq_le_telescope hn) hK
      have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      push_cast
      simp only [div_eq_mul_inv, one_mul] at ht
      have heq : (n : ℝ) + 1 - 1 = (n : ℝ) := by ring
      rw [heq]
      push_cast at hs
      simp only [div_eq_mul_inv] at ih hs ⊢
      linarith
  have hbound (n : ℕ) (hn : 2 ≤ n) :
      (A - H) * Real.log n ≤ C - W 2 + A * Real.log 2 + K := by
    have hl := hlower n hn
    have hu := hupper n hn
    have hr : 0 ≤ K / ((n : ℝ) - 1) := by
      have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
      exact div_nonneg hK (by linarith)
    nlinarith
  by_contra hnot
  have hdelta : 0 < A - H := by linarith
  let M : ℝ := (C - W 2 + A * Real.log 2 + K) / (A - H)
  obtain ⟨n, hn⟩ := exists_nat_gt (max 2 (Real.exp M))
  have hn2 : 2 ≤ n := by
    have hh : (2 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
    exact_mod_cast (le_of_lt hh)
  have hnexp : Real.exp M < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hlog : M < Real.log n := by
    simpa only [Real.log_exp] using Real.strictMonoOn_log
      (Real.exp_pos M) (lt_trans (Real.exp_pos M) hnexp) hnexp
  have hm := (div_lt_iff₀ hdelta).1 hlog
  have hb := hbound n hn2
  nlinarith

/-- Logarithmic upper bounds determine their scalar growth coefficients. -/
theorem log_coefficient_le {A H C : ℝ}
    (hupper : ∀ n : ℕ, 2 ≤ n → A * Real.log n ≤ H * Real.log n + C) : A ≤ H := by
  by_contra hnot
  have hdelta : 0 < A - H := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (max 2 (Real.exp (C / (A - H))))
  have hn2 : 2 ≤ n := by
    have hh : (2 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
    exact_mod_cast (le_of_lt hh)
  have hnexp : Real.exp (C / (A - H)) < n :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have hlog : C / (A - H) < Real.log n := by
    simpa only [Real.log_exp] using Real.strictMonoOn_log
      (Real.exp_pos _) (lt_trans (Real.exp_pos _) hnexp) hnexp
  have hm := (div_lt_iff₀ hdelta).1 hlog
  have hu := hupper n hn2
  nlinarith

/-- A fixed multiplicative constant cannot hide a larger power exponent. -/
theorem rpow_exponent_le {A H K : ℝ} (hK : 0 < K)
    (hupper : ∀ n : ℕ, 2 ≤ n → (n : ℝ) ^ A ≤ K * (n : ℝ) ^ H) : A ≤ H := by
  apply log_coefficient_le (C := Real.log K)
  intro n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hn0 A) (hupper n hn)
  rw [Real.log_rpow hn0, Real.log_mul (ne_of_gt hK)
    (ne_of_gt (Real.rpow_pos_of_pos hn0 H)), Real.log_rpow hn0] at hl
  linarith

#print axioms growth_coefficient_le
#print axioms rpow_exponent_le

end Matmul.DiscretePotential
