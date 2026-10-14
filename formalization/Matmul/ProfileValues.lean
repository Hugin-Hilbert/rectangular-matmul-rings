import Matmul.ConvolutionCharacter
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Scalar profiles of an actual integral character

The two profiles are geometric means of the oriented convolution values.
Their positivity, monotonicity, rank bounds, and boundary powers follow from
the coefficient-level character and the integral convolution restrictions.
-/

namespace Matmul.ProfileValues

open Matmul.ConvolutionCharacter

noncomputable section

/-- The average exponent on the first two tensor legs. -/
def a (φ : IntegralCharacter) : ℝ := (φ.pX + φ.pY) / 2

/-- The exponent on the third tensor leg. -/
def b (φ : IntegralCharacter) : ℝ := φ.pZ

/-- The symmetric convolution profile. -/
def rawV (φ : IntegralCharacter) (r s : ℕ) : ℝ :=
  Real.sqrt (valueXY φ r s * valueXY φ s r)

/-- The oriented convolution profile. -/
def rawU (φ : IntegralCharacter) (r s : ℕ) : ℝ :=
  Real.sqrt (valueXZ φ r s * valueYZ φ r s)

theorem a_nonneg (φ : IntegralCharacter) : 0 ≤ a φ := by
  dsimp [a]
  linarith [φ.pX_nonneg, φ.pY_nonneg]

theorem a_le_one (φ : IntegralCharacter) : a φ ≤ 1 := by
  dsimp [a]
  linarith [φ.pX_le_one, φ.pY_le_one]

theorem b_nonneg (φ : IntegralCharacter) : 0 ≤ b φ := φ.pZ_nonneg

theorem b_le_one (φ : IntegralCharacter) : b φ ≤ 1 := φ.pZ_le_one

/-- A geometric mean preserves coordinatewise inequalities between
nonnegative values. -/
theorem sqrt_mul_mono {x x' y y' : ℝ}
    (hx : 0 ≤ x) (hy' : 0 ≤ y') (hxx' : x ≤ x') (hyy' : y ≤ y') :
    Real.sqrt (x * y) ≤ Real.sqrt (x' * y') :=
  Real.sqrt_le_sqrt ((mul_le_mul_of_nonneg_left hyy' hx).trans
    (mul_le_mul_of_nonneg_right hxx' hy'))

/-- A common nonnegative upper bound bounds the geometric mean. -/
theorem sqrt_mul_le {x y B : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxB : x ≤ B) (hyB : y ≤ B) : Real.sqrt (x * y) ≤ B := by
  have hB : 0 ≤ B := hx.trans hxB
  calc
    Real.sqrt (x * y) ≤ Real.sqrt (B * B) :=
      Real.sqrt_le_sqrt (mul_le_mul hxB hyB hy hB)
    _ = B := by rw [← pow_two, Real.sqrt_sq hB]

theorem rawV_nonneg (φ : IntegralCharacter) (r s : ℕ) : 0 ≤ rawV φ r s :=
  Real.sqrt_nonneg _

theorem rawU_nonneg (φ : IntegralCharacter) (r s : ℕ) : 0 ≤ rawU φ r s :=
  Real.sqrt_nonneg _

theorem rawV_pos (φ : IntegralCharacter) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    0 < rawV φ r s := by
  exact Real.sqrt_pos.2 (mul_pos (valueXY_pos φ r s hr hs) (valueXY_pos φ s r hs hr))

theorem rawU_pos (φ : IntegralCharacter) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    0 < rawU φ r s := by
  exact Real.sqrt_pos.2 (mul_pos (valueXZ_pos φ r s hr hs) (valueYZ_pos φ r s hr hs))

theorem rawV_le (φ : IntegralCharacter) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    rawV φ r s ≤ (r : ℝ) + s - 1 := by
  apply sqrt_mul_le (valueXY_pos φ r s hr hs).le (valueXY_pos φ s r hs hr).le
    (valueXY_le φ r s hr hs)
  simpa only [add_comm] using valueXY_le φ s r hs hr

theorem rawU_le (φ : IntegralCharacter) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    rawU φ r s ≤ (r : ℝ) + s - 1 :=
  sqrt_mul_le (valueXZ_pos φ r s hr hs).le (valueYZ_pos φ r s hr hs).le
    (valueXZ_le φ r s hr hs) (valueYZ_le φ r s hr hs)

theorem rawV_mono_first (φ : IntegralCharacter) (r r' s : ℕ) (hrr' : r ≤ r') :
    rawV φ r s ≤ rawV φ r' s := by
  apply sqrt_mul_mono
  · exact valueXY_nonneg φ r s
  · exact valueXY_nonneg φ s r'
  · exact valueXY_mono_first φ r r' s hrr'
  · exact valueXY_mono_second φ s r r' hrr'

theorem rawV_mono_second (φ : IntegralCharacter) (r s s' : ℕ) (hss' : s ≤ s') :
    rawV φ r s ≤ rawV φ r s' := by
  apply sqrt_mul_mono
  · exact valueXY_nonneg φ r s
  · exact valueXY_nonneg φ s' r
  · exact valueXY_mono_second φ r s s' hss'
  · exact valueXY_mono_first φ s s' r hss'

theorem rawU_mono_first (φ : IntegralCharacter) (r r' s : ℕ) (hrr' : r ≤ r') :
    rawU φ r s ≤ rawU φ r' s := by
  apply sqrt_mul_mono
  · exact valueXZ_nonneg φ r s
  · exact valueYZ_nonneg φ r' s
  · exact valueXZ_mono_first φ r r' s hrr'
  · exact valueYZ_mono_first φ r r' s hrr'

theorem rawU_mono_second (φ : IntegralCharacter) (r s s' : ℕ) (hss' : s ≤ s') :
    rawU φ r s ≤ rawU φ r s' := by
  apply sqrt_mul_mono
  · exact valueXZ_nonneg φ r s
  · exact valueYZ_nonneg φ r s'
  · exact valueXZ_mono_second φ r s s' hss'
  · exact valueYZ_mono_second φ r s s' hss'

theorem rawV_symm (φ : IntegralCharacter) (r s : ℕ) : rawV φ r s = rawV φ s r := by
  simp only [rawV, mul_comm]

/-- The geometric mean of two powers has their averaged exponent. -/
theorem sqrt_mul_rpow {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Real.sqrt (t ^ x * t ^ y) = t ^ ((x + y) / 2) := by
  rw [← Real.rpow_add ht, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
  congr 1
  ring

theorem rawV_one_left (φ : IntegralCharacter) (s : ℕ) (hs : 1 ≤ s) :
    rawV φ 1 s = (s : ℝ) ^ a φ := by
  have hsR : 0 < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  rw [rawV, valueXY_one_left φ s hs, valueXY_one_right φ s hs]
  exact sqrt_mul_rpow hsR φ.pX φ.pY

theorem rawV_one_right (φ : IntegralCharacter) (r : ℕ) (hr : 1 ≤ r) :
    rawV φ r 1 = (r : ℝ) ^ a φ := by
  rw [rawV_symm]
  exact rawV_one_left φ r hr

theorem rawU_one_left (φ : IntegralCharacter) (s : ℕ) (hs : 1 ≤ s) :
    rawU φ 1 s = (s : ℝ) ^ a φ := by
  have hsR : 0 < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  rw [rawU, valueXZ_one_left φ s hs, valueYZ_one_left φ s hs]
  exact sqrt_mul_rpow hsR φ.pX φ.pY

theorem rawU_one_right (φ : IntegralCharacter) (r : ℕ) (hr : 1 ≤ r) :
    rawU φ r 1 = (r : ℝ) ^ b φ := by
  rw [rawU, valueXZ_one_right φ r hr, valueYZ_one_right φ r hr]
  rw [← pow_two, Real.sqrt_sq (Real.rpow_nonneg (by positivity) _)]
  rfl

theorem rawV_one_one (φ : IntegralCharacter) : rawV φ 1 1 = 1 := by
  simpa using rawV_one_left φ 1 (by omega)

theorem rawU_one_one (φ : IntegralCharacter) : rawU φ 1 1 = 1 := by
  simpa using rawU_one_right φ 1 (by omega)

#print axioms rawV_one_left
#print axioms rawU_one_left
#print axioms rawU_one_right
#print axioms rawV_mono_first

end
end Matmul.ProfileValues
