import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-!
# Polynomial tensor powers over a commutative semiring

Vanishing below a coefficient is preserved by tensor powers, and the first
possible coefficient is the tensor power of the original coefficient.
Restrictions commute with tensor powers using the explicit product matrices.
-/

namespace Matmul.PolynomialPower

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

variable {K : Type*} [CommSemiring K]

/-- The first possible coefficient in a product of polynomials is the product
of their first possible coefficients. This holds without division or any
assumption that the coefficient semiring is a domain. -/
theorem coeff_prod_of_low_zero {ι : Type*} [Fintype ι]
    (f : ι → Polynomial K) (ℓ : ℕ)
    (hlow : ∀ i d, d < ℓ → (f i).coeff d = 0) :
    (∏ i, f i).coeff (Fintype.card ι * ℓ) = ∏ i, (f i).coeff ℓ := by
  classical
  have hdvd (i : ι) : Polynomial.X ^ ℓ ∣ f i :=
    Polynomial.X_pow_dvd_iff.mpr (hlow i)
  choose g hg using hdvd
  have hprod : (∏ i, f i) =
      Polynomial.X ^ (Fintype.card ι * ℓ) * ∏ i, g i := by
    simp_rw [hg, Finset.prod_mul_distrib]
    simp [← pow_mul, Nat.mul_comm]
  have hgcoeff (i : ι) : (f i).coeff ℓ = (g i).coeff 0 := by
    rw [hg i]
    simpa only [Nat.zero_add] using Polynomial.coeff_X_pow_mul (g i) ℓ 0
  rw [hprod]
  calc
    (Polynomial.X ^ (Fintype.card ι * ℓ) * ∏ i, g i).coeff
        (Fintype.card ι * ℓ) = (∏ i, g i).coeff 0 := by
      simpa only [Nat.zero_add] using
        Polynomial.coeff_X_pow_mul (∏ i, g i) (Fintype.card ι * ℓ) 0
    _ = ∏ i, (f i).coeff ℓ := by
      rw [Polynomial.coeff_zero_prod]
      simp only [hgcoeff]

/-- A tensor power has the tensor power of the original coefficient as its
coefficient at the multiplied vanishing order. -/
theorem tensor_power_leading_coeff {X Y Z : Type*}
    (F : Tensor (Polynomial K) X Y Z) (U : Tensor K X Y Z) (ℓ m : ℕ)
    (hlow : ∀ x y z d, d < ℓ → (F x y z).coeff d = 0)
    (hlead : ∀ x y z, (F x y z).coeff ℓ = U x y z) :
    (fun x y z => (Tensor.power F m x y z).coeff (m * ℓ)) =
      Tensor.power U m := by
  classical
  funext x y z
  dsimp only [Tensor.power]
  simpa only [Fintype.card_fin, hlead] using
    coeff_prod_of_low_zero (fun i : Fin m => F (x i) (y i) (z i)) ℓ
      (fun i d hd => hlow (x i) (y i) (z i) d hd)

/-- Expanding a product of three nested sums amounts to choosing one
coordinate from each leg at every factor. -/
theorem prod_three_sums {I X Y Z : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] [Fintype Z]
    (f : I → X → Y → Z → K) :
    (∏ i, ∑ x, ∑ y, ∑ z, f i x y z) =
      ∑ x : I → X, ∑ y : I → Y, ∑ z : I → Z,
        ∏ i, f i (x i) (y i) (z i) := by
  classical
  let e : (I → X × Y × Z) ≃ (I → X) × (I → Y) × (I → Z) :=
    (Equiv.arrowProdEquivProdArrow I (fun _ => X) (fun _ => Y × Z)).trans
      (Equiv.prodCongr (Equiv.refl (I → X))
        (Equiv.arrowProdEquivProdArrow I (fun _ => Y) (fun _ => Z)))
  calc
    (∏ i, ∑ x, ∑ y, ∑ z, f i x y z) =
        ∏ i, ∑ p : X × Y × Z, f i p.1 p.2.1 p.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ p : I → X × Y × Z, ∏ i, f i (p i).1 (p i).2.1 (p i).2.2 :=
      Fintype.prod_sum _
    _ = ∑ p : (I → X) × (I → Y) × (I → Z),
        ∏ i, f i (p.1 i) (p.2.1 i) (p.2.2 i) := by
      apply Fintype.sum_equiv e
      intro p
      rfl
    _ = _ := by simp only [Fintype.sum_prod_type]

/-- Tensor powers of a restriction are restricted tensor powers. The three
restriction matrices are the products of the original matrix entries. -/
theorem tensor_restrict_power {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) (m : ℕ) :
    Tensor.power (Tensor.restrict A B C T) m =
      Tensor.restrict
        (fun x' x => ∏ i, A (x' i) (x i))
        (fun y' y => ∏ i, B (y' i) (y i))
        (fun z' z => ∏ i, C (z' i) (z i))
        (Tensor.power T m) := by
  classical
  funext x' y' z'
  simp only [Tensor.power, Tensor.restrict]
  rw [prod_three_sums]
  simp only [Finset.prod_mul_distrib]

#print axioms coeff_prod_of_low_zero
#print axioms tensor_power_leading_coeff
#print axioms tensor_restrict_power

end Matmul.PolynomialPower
