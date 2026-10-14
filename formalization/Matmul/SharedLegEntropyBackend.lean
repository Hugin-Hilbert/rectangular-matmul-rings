import Matmul.SharedLegEntropy
import Matmul.IntegralConvolutionSeparator

/-!
# The complete integral shared-leg entropy backend

The polynomial degeneration property is obtained by actual integer coefficient
extraction.  The convolution bound follows from exact integer decompositions
of all tensor powers.  The public entropy theorems below have neither backend
property among their hypotheses.
-/

namespace Matmul.SharedLegEntropyBackend

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open Matmul.SharedLegEntropy
open scoped BigOperators

noncomputable section

/-- Integral convolution has the optimal character bound: the fixed
denominator-clearing factor disappears after tensor powering. -/
theorem separatorConvolution_value_le (φ : IntegralCharacter) (M : ℕ) (hM : 0 < M) :
    φ.value (IntegralSeparator.convolution ℤ M) ≤ ((4 * M - 3 : ℕ) : ℝ) := by
  obtain ⟨K, _, hK⟩ := IntegralConvolution.exists_separator_power_rank_bound M hM
  apply le_of_pow_le_const_mul_pow (C := (K : ℝ))
    (by positivity : (0 : ℝ) ≤ ((4 * M - 3 : ℕ) : ℝ))
  intro m
  have h := φ.value_le_rank (hK m)
  rw [φ.value_power] at h
  simpa only [Nat.cast_mul, Nat.cast_pow] using h

theorem separatorConvolution_value_le_five (φ : IntegralCharacter) :
    ∀ M : ℕ, 0 < M → φ.value (IntegralSeparator.convolution ℤ M) ≤ 5 * (M : ℝ) := by
  intro M hM
  apply (separatorConvolution_value_le φ M hM).trans
  exact_mod_cast (show 4 * M - 3 ≤ 5 * M by omega)

variable {s : ℕ} {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- Shared-leg entropy over the actual integral tensor character, with both
algebraic backends discharged by proved integer constructions. -/
theorem fullSharedFirst_tag (φ : IntegralCharacter)
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor ℤ X Y Z)
    (hB : ∀ a, 0 < φ.value (B a)) :
    Real.exp (φ.pX * finiteEntropy q.mass) *
        ∏ a, φ.value (B a) ^ q.mass a ≤ φ.value (sharedFirstTensor B) :=
  sharedFirst_tag φ (polynomialRestrictionMonotone φ)
    (separatorConvolution_value_le_five φ) q B hB

theorem fullLogSharedFirst_tag (φ : IntegralCharacter)
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor ℤ X Y Z)
    (hB : ∀ a, 0 < φ.value (B a)) :
    φ.pX * finiteEntropy q.mass + ∑ a, q.mass a * Real.log (φ.value (B a)) ≤
      Real.log (φ.value (sharedFirstTensor B)) :=
  log_sharedFirst_tag φ (polynomialRestrictionMonotone φ)
    (separatorConvolution_value_le_five φ) q B hB

section Dependent

variable {U V : Fin s → Type} [∀ a, Fintype (U a)] [∀ a, Fintype (V a)]

theorem fullDependent_tag (φ : IntegralCharacter)
    (q : FiniteLaw (Fin s)) (B : ∀ a, Tensor ℤ X (U a) (V a))
    (hB : ∀ a, 0 < φ.value (B a)) :
    Real.exp (φ.pX * finiteEntropy q.mass) *
        ∏ a, φ.value (B a) ^ q.mass a ≤ φ.value (sharedFirstDependentTensor B) :=
  sharedFirstDependent_tag φ (polynomialRestrictionMonotone φ)
    (separatorConvolution_value_le_five φ) q B hB

theorem fullLogDependent_tag (φ : IntegralCharacter)
    (q : FiniteLaw (Fin s)) (B : ∀ a, Tensor ℤ X (U a) (V a))
    (hB : ∀ a, 0 < φ.value (B a)) :
    φ.pX * finiteEntropy q.mass + ∑ a, q.mass a * Real.log (φ.value (B a)) ≤
      Real.log (φ.value (sharedFirstDependentTensor B)) :=
  log_sharedFirstDependent_tag φ (polynomialRestrictionMonotone φ)
    (separatorConvolution_value_le_five φ) q B hB

end Dependent

/-- Explicitly connected to every monotone spectral point on actual
unit-admitting integral tensor classes. -/
theorem spectralSharedFirst_tag
    (χ : Matmul.IntegralSpectrum.Character) (hχ : Monotone χ)
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor ℤ X Y Z)
    (hB : ∀ a, 0 < (IntegralCharacter.ofUnitTensorClassHom χ hχ).value (B a)) :
    Real.exp (IntegerCharacter.pX χ * finiteEntropy q.mass) *
        ∏ a, (IntegralCharacter.ofUnitTensorClassHom χ hχ).value (B a) ^ q.mass a ≤
      (IntegralCharacter.ofUnitTensorClassHom χ hχ).value (sharedFirstTensor B) := by
  simpa only [IntegralCharacter.pX_ofUnitTensorClassHom] using
    fullSharedFirst_tag (IntegralCharacter.ofUnitTensorClassHom χ hχ) q B hB

#print axioms separatorConvolution_value_le
#print axioms fullSharedFirst_tag
#print axioms fullDependent_tag
#print axioms spectralSharedFirst_tag

end
end Matmul.SharedLegEntropyBackend
