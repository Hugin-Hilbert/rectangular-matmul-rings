import Matmul.ProfileValues
import Matmul.MatrixPowerBound
import Matmul.RectangularOptimization

/-!
# Actual integral character values of rectangular matrix multiplication

Three oriented dot tensors give the matrix tensor by explicit bijections
of its coordinate spaces.  The resulting power law agrees with the original
spectral point on the actual integral matrix class.
-/

namespace Matmul.MatrixCharacter

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Matmul.IntegralCharacter Matmul.IntegerCharacter Matmul.IntegerBilinear

noncomputable section

def tripleDot (a b c : ℕ) :=
  Tensor.product (Tensor.product (cyclic (cyclic (dotX a))) (cyclic (dotX b)))
    (dotX c)

def matrixXEquiv (a b : ℕ) :
    (Fin a × Fin b) ≃ ((Fin a × Fin b) × PUnit.{1}) :=
  (Equiv.prodPUnit (Fin a × Fin b)).symm

def matrixYEquiv (b c : ℕ) :
    (Fin b × Fin c) ≃ ((PUnit.{1} × Fin b) × Fin c) :=
  Equiv.prodCongr (Equiv.punitProd (Fin b)).symm (Equiv.refl (Fin c))

def matrixZEquiv (c a : ℕ) :
    (Fin c × Fin a) ≃ ((Fin a × PUnit.{1}) × Fin c) :=
  (Equiv.prodComm (Fin c) (Fin a)).trans
    (Equiv.prodCongr (Equiv.prodPUnit (Fin a)).symm (Equiv.refl (Fin c)))

/-- Matrix multiplication is exactly the reindexed product of three dots. -/
theorem tripleDot_matrixTensor (a b c : ℕ) :
    Tensor.pullback (matrixXEquiv a b) (matrixYEquiv b c) (matrixZEquiv c a)
      (tripleDot a b c) = matrixTensor a b c := by
  funext x y z
  change ((if z.2 = x.1 then (1 : ℤ) else 0) *
    (if x.2 = y.1 then 1 else 0)) * (if y.2 = z.1 then 1 else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  have hguard : ((z.2 = x.1 ∧ x.2 = y.1) ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) := by tauto
  simp only [ite_zero_mul_ite_zero, one_mul, hguard]

theorem value_matrixTensor (φ : IntegralCharacter) {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    φ.value (matrixTensor a b c) =
      (a : ℝ) ^ φ.pY * (b : ℝ) ^ φ.pZ * (c : ℝ) ^ φ.pX := by
  rw [← tripleDot_matrixTensor a b c, φ.value_reindex]
  simp only [tripleDot, φ.map_product, φ.value_cyclic_cyclic_dotX ha,
    φ.value_cyclic_dotX hb, φ.value_dotX hc]

theorem value_symmetric_matrixTensor (φ : IntegralCharacter) {q inner : ℕ}
    (hq : 0 < q) (hi : 0 < inner) :
    φ.value (matrixTensor q inner q) =
      (q : ℝ) ^ (2 * ProfileValues.a φ) * (inner : ℝ) ^ φ.pZ := by
  rw [value_matrixTensor φ hq hi hq]
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hpow : (q : ℝ) ^ (2 * ProfileValues.a φ) =
      (q : ℝ) ^ φ.pY * (q : ℝ) ^ φ.pX := by
    have hsum : 2 * ProfileValues.a φ = φ.pY + φ.pX := by
      dsimp [ProfileValues.a]
      ring
    rw [hsum, Real.rpow_add hqR]
  rw [hpow]
  ring

/-- Agreement with the original spectral point on its matrix tensor class. -/
theorem value_matrixClass (χ : Matmul.IntegralSpectrum.Character) (hχ : Monotone χ)
    (a b c : ℕ) :
    (ofUnitTensorClassHom χ hχ).value (matrixTensor a b c) =
      χ (UnitTensorClass.matrixClass a b c) := by
  exact ofUnitTensorClassHom_value_ofZeroOneTensor χ hχ _ _

theorem matrixClass_power_law (χ : Matmul.IntegralSpectrum.Character)
    (hχ : Monotone χ) {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    χ (UnitTensorClass.matrixClass a b c) =
      (a : ℝ) ^ (ofUnitTensorClassHom χ hχ).pY *
      (b : ℝ) ^ (ofUnitTensorClassHom χ hχ).pZ *
      (c : ℝ) ^ (ofUnitTensorClassHom χ hχ).pX := by
  rw [← value_matrixClass χ hχ]
  exact value_matrixTensor _ ha hb hc

/-- A bound on the dot exponents gives a rounded matrix-value bound. -/
theorem value_ceil_matrixTensor_le (φ : IntegralCharacter) {q : ℕ} (hq : 2 ≤ q)
    {k F : ℝ} (hk : 0 ≤ k) (hF : 2 * ProfileValues.a φ + k * φ.pZ ≤ F) :
    φ.value (matrixTensor q (Nat.ceil ((q : ℝ) ^ k)) q) ≤ 2 * (q : ℝ) ^ F := by
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hi : 0 < Nat.ceil ((q : ℝ) ^ k) := by
    have hceil := Nat.le_ceil ((q : ℝ) ^ k)
    have hpow := Real.one_le_rpow hqR hk
    by_contra h
    have hz : Nat.ceil ((q : ℝ) ^ k) = 0 := by omega
    rw [hz, Nat.cast_zero] at hceil
    linarith
  rw [value_symmetric_matrixTensor φ (by omega) hi]
  exact MatrixPowerBound.ceil_rpow_bound hq hk φ.pZ_nonneg φ.pZ_le_one hF

/-- The analytic target is used only after the exponent inequality is proved. -/
theorem value_rectangular_matrixTensor_le (φ : IntegralCharacter) {q : ℕ}
    (hq : 2 ≤ q) {k : ℝ} (hk : 0 ≤ k)
    (hbound : 2 * ProfileValues.a φ + k * φ.pZ ≤
      RectangularOptimization.rectangularBound k) :
    φ.value (matrixTensor q (Nat.ceil ((q : ℝ) ^ k)) q) ≤
      2 * (q : ℝ) ^ RectangularOptimization.rectangularBound k :=
  value_ceil_matrixTensor_le φ hq hk hbound

theorem matrixClass_ceil_le (χ : Matmul.IntegralSpectrum.Character)
    (hχ : Monotone χ) {q : ℕ} (hq : 2 ≤ q) {k F : ℝ} (hk : 0 ≤ k)
    (hF : 2 * ProfileValues.a (ofUnitTensorClassHom χ hχ) +
      k * (ofUnitTensorClassHom χ hχ).pZ ≤ F) :
    χ (UnitTensorClass.matrixClass q (Nat.ceil ((q : ℝ) ^ k)) q) ≤
      2 * (q : ℝ) ^ F := by
  rw [← value_matrixClass χ hχ]
  exact value_ceil_matrixTensor_le _ hq hk hF

#print axioms tripleDot_matrixTensor
#print axioms value_matrixTensor
#print axioms matrixClass_power_law
#print axioms value_rectangular_matrixTensor_le
#print axioms matrixClass_ceil_le

end
end Matmul.MatrixCharacter
