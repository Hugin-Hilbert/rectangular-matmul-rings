import Matmul.IntegerProfileLaws
import Matmul.DiscreteParameterCap
import Matmul.ConvolutionDotRestriction

/-! The rectangular cap for actual integral tensor characters. -/

namespace Matmul.IntegerProfileCap

open OAI.MatrixMultiplication.AuxiliarySeparation
open Matmul.ProfileValues Matmul.IntegerProfileLaws
open Matmul.DiscreteProfiles

noncomputable section

theorem poweredV_pos (φ : IntegralCharacter) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    0 < poweredV φ r s := Real.rpow_pos_of_pos (rawV_pos φ r s hr hs) _

theorem poweredU_pos (φ : IntegralCharacter) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    0 < poweredU φ r s := Real.rpow_pos_of_pos (rawU_pos φ r s hr hs) _

theorem poweredV_boundary (φ : IntegralCharacter) (ha : 0 < a φ)
    (s : ℕ) (hs : 1 ≤ s) : poweredV φ 1 s = (s : ℝ) := by
  rw [poweredV, rawV_one_left φ s hs]
  simpa only [one_div] using Real.rpow_rpow_inv (Nat.cast_nonneg s) ha.ne'

theorem poweredU_boundary (φ : IntegralCharacter) (n : ℕ) (hn : 1 ≤ n) :
    poweredU φ n 1 = (n : ℝ) ^ (b φ / a φ) := by
  rw [poweredU, rawU_one_right φ n hn, ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  ring

theorem poweredU_theta_root (φ : IntegralCharacter) (ha : 0 < a φ) (hb : 0 < b φ)
    (r s : ℕ) : poweredU φ r s ^ (1 / (b φ / a φ)) = rawU φ r s ^ (1 / b φ) := by
  rw [poweredU, ← Real.rpow_mul (rawU_nonneg φ r s)]
  congr 1
  field_simp [ha.ne', hb.ne']

/-- Every positive-average integral character supplies the full discrete profile data. -/
theorem actualDiscreteData (φ : IntegralCharacter) (ha : 0 < a φ) :
    DiscreteData (poweredV φ) (poweredU φ) (1 / a φ) (b φ / a φ) where
  p_ge_one := by
    apply (le_div_iff₀ ha).mpr
    simpa using a_le_one φ
  theta_nonneg := div_nonneg (b_nonneg φ) ha.le
  P_pos := poweredV_pos φ
  Q_pos := poweredU_pos φ
  P_symm := by
    intro r s hr hs
    simp only [poweredV, rawV_symm φ r s]
  P_boundary := poweredV_boundary φ ha
  Q_boundary := poweredU_boundary φ
  P_mono_first := by
    intro r r' s hr hrr' hs
    exact Real.rpow_le_rpow (rawV_nonneg φ r s) (rawV_mono_first φ r r' s hrr')
      (one_div_nonneg.mpr ha.le)
  P_mono_second := by
    intro r s s' hr hs hss'
    exact Real.rpow_le_rpow (rawV_nonneg φ r s) (rawV_mono_second φ r s s' hss')
      (one_div_nonneg.mpr ha.le)
  Q_mono_first := by
    intro r r' s hr hrr' hs
    exact Real.rpow_le_rpow (rawU_nonneg φ r s) (rawU_mono_first φ r r' s hrr')
      (one_div_nonneg.mpr ha.le)
  Q_mono_second := by
    intro r s s' hr hs hss'
    exact Real.rpow_le_rpow (rawU_nonneg φ r s) (rawU_mono_second φ r s s' hss')
      (one_div_nonneg.mpr ha.le)
  P_concave_first := V_concave_first φ ha
  P_concave_second := V_concave_second φ ha
  Q_concave_second := U_concave_second φ ha
  Q_concave_first := by
    intro htheta s hs
    have hb : 0 < b φ := by
      have h := (div_pos_iff).mp htheta
      rcases h with h | h
      · exact h.1
      · exact False.elim (not_lt_of_ge ha.le h.2)
    simpa only [poweredU_theta_root φ ha hb] using U_concave_first φ hb s hs
  P_tripling := V_tripling φ ha
  Q_tripling := U_tripling φ ha
  Q_self_tripling := by
    intro htheta r s hr hs
    have hb : 0 < b φ := by
      have h := (div_pos_iff).mp htheta
      rcases h with h | h
      · exact h.1
      · exact False.elim (not_lt_of_ge ha.le h.2)
    simpa only [poweredU_theta_root φ ha hb] using U_self_tripling φ hb r s hr hs
  P_rank_upper := by
    intro r s hr hs
    exact Real.rpow_le_rpow (rawV_nonneg φ r s) (rawV_le φ r s hr hs)
      (one_div_nonneg.mpr ha.le)
  Q_rank_upper := by
    intro r s hr hs
    exact Real.rpow_le_rpow (rawU_nonneg φ r s) (rawU_le φ r s hr hs)
      (one_div_nonneg.mpr ha.le)

/-- The parabolic cap is realized by actual integral convolution profiles. -/
theorem actual_integer_character_cap_of_pos (φ : IntegralCharacter) (ha : 0 < a φ) :
    b φ ≤ 4 * a φ * (1 - a φ) :=
  parameter_cap ha (actualDiscreteData φ ha)

/-- The exact rectangular objective for every character with positive average exponent. -/
theorem rectangular_objective_le_of_pos (φ : IntegralCharacter) (ha : 0 < a φ)
    (k : ℝ) (hk : 0 ≤ k) :
    2 * a φ + k * b φ ≤ Matmul.RectangularOptimization.rectangularBound k :=
  rectangular_objective_le ha (b_nonneg φ) hk (actualDiscreteData φ ha)

/-- The genuine dot restriction eliminates the zero-average endpoint. -/
theorem b_eq_zero_of_square_le_one (φ : IntegralCharacter)
    (hbound : rawV φ 2 2 ≤ 1) : b φ = 0 := by
  have hdot := Matmul.ConvolutionDotRestriction.rawV_square_lower φ 2 (by omega)
  have hpower : (2 : ℝ) ^ b φ ≤ (2 : ℝ) ^ (0 : ℝ) := by
    simpa only [b, Nat.cast_ofNat, Real.rpow_zero] using hdot.trans hbound
  have hb : b φ ≤ 0 :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hpower
  exact le_antisymm hb (b_nonneg φ)

/-- Every actual integral tensor character satisfies the shared-leg parabola. -/
theorem actual_integer_character_cap (φ : IntegralCharacter) :
    b φ ≤ 4 * a φ * (1 - a φ) := by
  by_cases ha : 0 < a φ
  · exact actual_integer_character_cap_of_pos φ ha
  · have ha0 : a φ = 0 := le_antisymm (not_lt.mp ha) (a_nonneg φ)
    have hb0 := b_eq_zero_of_square_le_one φ (rawV_two_two_le_of_a_zero φ ha0)
    simp [ha0, hb0]

/-- The exact rectangular objective holds without a positivity proviso. -/
theorem actual_rectangular_objective_le (φ : IntegralCharacter) (k : ℝ) (hk : 0 ≤ k) :
    2 * a φ + k * b φ ≤ Matmul.RectangularOptimization.rectangularBound k :=
  Matmul.RectangularOptimization.objective_le (a_nonneg φ) (a_le_one φ)
    (b_nonneg φ) (actual_integer_character_cap φ) hk

#print axioms actualDiscreteData
#print axioms actual_integer_character_cap
#print axioms actual_rectangular_objective_le

end
end Matmul.IntegerProfileCap
