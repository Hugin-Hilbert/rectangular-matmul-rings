import Matmul.ProfileValues
import Mathlib.Data.Fin.Rev

/-!
# A diagonal-output restriction of integral convolution

Selecting coefficient `n - 1` and reversing the second input gives a dot
product.  This is an actual coordinate restriction over the integers.
-/

namespace Matmul.ConvolutionDotRestriction

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Matmul.IntegralCharacter Matmul.IntegerCharacter
open Matmul.IntegralConvolution Matmul.ConvolutionCharacter Matmul.ProfileValues

noncomputable section

def middleOutput (n : ℕ) (hn : 1 ≤ n) : PUnit.{1} → Fin (outputLength n n) :=
  fun _ => ⟨n - 1, by unfold outputLength; omega⟩

/-- The middle convolution coefficient pairs opposite input indices. -/
theorem pullback_middle_output (n : ℕ) (hn : 1 ≤ n) :
    Tensor.pullback id Fin.rev (middleOutput n hn) (CXY n n) =
      cyclic (dotX n) := by
  funext x y z
  have heq : x.val + y.rev.val = n - 1 ↔ x = y := by
    rw [Fin.val_rev, Fin.ext_iff]
    have hy := y.isLt
    omega
  change (if x.val + y.rev.val = n - 1 then (1 : ℤ) else 0) =
    if x = y then 1 else 0
  simp only [heq]

/-- The dot tensor with a scalar output is an integral restriction. -/
theorem dotZ_restrict_square (n : ℕ) (hn : 1 ≤ n) :
    IsRestriction (cyclic (dotX n)) (CXY n n) := by
  rw [← pullback_middle_output n hn]
  exact IsRestriction.pullback _ _ _ _

theorem valueXY_square_lower (φ : IntegralCharacter) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ φ.pZ ≤ valueXY φ n n := by
  rw [← φ.value_cyclic_dotX (by omega : 0 < n), valueXY,
    ← pullback_middle_output n hn]
  exact φ.value_pullback_le _ _ _ _

theorem rawV_square_eq (φ : IntegralCharacter) (n : ℕ) :
    rawV φ n n = valueXY φ n n := by
  rw [rawV, ← pow_two, Real.sqrt_sq (valueXY_nonneg φ n n)]

theorem rawV_square_lower (φ : IntegralCharacter) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ φ.pZ ≤ rawV φ n n := by
  rw [rawV_square_eq]
  exact valueXY_square_lower φ n hn

#print axioms dotZ_restrict_square
#print axioms valueXY_square_lower
#print axioms rawV_square_lower

end
end Matmul.ConvolutionDotRestriction
