import Matmul.IntegralConvolutionInterpolation
import Matmul.FiniteAlgebraDescent
import Mathlib.RingTheory.PowerBasis

/-!
# Powers of scaled integral convolution certificates

The scalar multiplier is powered, while the finite algebra is kept fixed.
-/

namespace Matmul.IntegralConvolution

set_option backward.isDefEq.respectTransparency false

open OAI.MatrixMultiplication.Foundation Module
open scoped BigOperators

theorem tensor_power_scale {B X Y Z : Type*} [CommSemiring B]
    (T : Tensor B X Y Z) (E : B) (m : ℕ) :
    Tensor.power (fun x y z => E * T x y z) m =
      fun x y z => E ^ m * Tensor.power T m x y z := by
  funext x y z
  simp only [Tensor.power, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- The coordinate of one in an integer power basis is an actual integer
linear retraction, including when the algebra has zero divisors. -/
theorem powerBasis_coord_zero_one {B : Type*} [CommRing B]
    (pb : PowerBasis ℤ B) (hd : 0 < pb.dim) :
    pb.basis.coord ⟨0, hd⟩ (1 : B) = 1 := by
  have hzero : pb.basis ⟨0, hd⟩ = (1 : B) := by
    rw [pb.basis_eq_pow]
    simp
  change pb.basis.repr (1 : B) ⟨0, hd⟩ = 1
  rw [← hzero, Basis.repr_self]
  simp

/-- A scaled rank certificate over one fixed integer power-basis algebra
gives integer certificates for all powers, with only a constant square
dimension overhead. -/
theorem scaled_integer_power_rank_of_base {B : Type*} [CommRing B]
    (pb : PowerBasis ℤ B) (hd : 0 < pb.dim) {r s : ℕ} (E : ℤ)
    (h : Tensor.RankAtMost
      (fun x y z => algebraMap ℤ B (E * convolution ℤ r s x y z))
      (outputLength r s)) (m : ℕ) :
    Tensor.RankAtMost
      (fun x y z => E ^ m * Tensor.power (convolution ℤ r s) m x y z)
      (outputLength r s ^ m * pb.dim * pb.dim) := by
  have hp := Matmul.FiniteAlgebraDescent.integer_power_rank_descent_of_base
    pb.basis (pb.basis.coord ⟨0, hd⟩) (powerBasis_coord_zero_one pb hd) h m
  rw [tensor_power_scale] at hp
  exact hp

#print axioms scaled_integer_power_rank_of_base

end Matmul.IntegralConvolution
