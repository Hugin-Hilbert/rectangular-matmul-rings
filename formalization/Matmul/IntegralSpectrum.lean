import Matmul.IntegerScalar
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.StateObstruction
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.MultiplicativeStates

/-!
# Spectral extraction on unit-admitting integer tensors

The imported compactness, separation, and fixed-point proofs are the generic
part of OpenAI's tensor-spectrum development. This file supplies their actual
integral tensor semiring interpretation. The absence of a scalar-gain
catalyst is stated explicitly; deriving it from an asymptotic-rank threshold
is a separate rank-obstruction theorem.
-/

namespace Matmul.IntegralSpectrum

open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring

noncomputable section

/-- A normalized additive and multiplicative valuation of unit-admitting
integer tensor classes, monotone under integral restriction. -/
abbrev Character := UnitTensorClass ℤ →+* ℝ

/-- The integral tensor semiring supplies every order and rank-domination
hypothesis required by the generic spectral extraction theorem. -/
theorem exists_detecting_character_of_no_catalyst
    (d : UnitTensorClass ℤ) (k : ℕ)
    (hno : ∀ (D s : UnitTensorClass ℤ) (m : ℕ), 0 < m →
      ¬ D + (m : UnitTensorClass ℤ) + d * s ≤ D + (k : UnitTensorClass ℤ) * s) :
    ∃ χ : Character, Monotone χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ UnitTensorClass.rank x) ∧ (k : ℝ) ≤ χ d := by
  have hne := normalizedStates_nonempty_of_no_catalyst
    UnitTensorClass.rank d k UnitTensorClass.zero_le UnitTensorClass.le_rank
    (fun _ _ _ _ h₁ h₂ => UnitTensorClass.add_mono h₁ h₂) hno
  have hdom (z x : UnitTensorClass ℤ) :
      z * x ≤ (UnitTensorClass.rank x : UnitTensorClass ℤ) * z := by
    calc
      z * x ≤ z * (UnitTensorClass.rank x : UnitTensorClass ℤ) :=
        UnitTensorClass.mul_mono le_rfl (UnitTensorClass.le_rank x)
      _ = _ := mul_comm _ _
  exact exists_monotone_semiringHom_of_normalizedStates
    UnitTensorClass.rank d (k : ℝ)
    (fun _ hz => UnitTensorClass.one_le_of_ne_zero hz)
    (fun _ _ _ h => UnitTensorClass.mul_mono le_rfl h) hdom hne

/-- Every normalized integral character is positive on a nonzero
unit-admitting class, without inverting a tensor coefficient. -/
theorem one_le_character_of_ne_zero (χ : Character) (hχ : Monotone χ)
    {T : UnitTensorClass ℤ} (hT : T ≠ 0) : 1 ≤ χ T := by
  simpa using hχ (UnitTensorClass.one_le_of_ne_zero hT)

/-- A character is bounded by an actual integral rank decomposition. -/
theorem character_le_rank (χ : Character) (hχ : Monotone χ)
    (T : UnitTensorClass ℤ) : χ T ≤ UnitTensorClass.rank T := by
  simpa using hχ (UnitTensorClass.le_rank T)

end
end Matmul.IntegralSpectrum
